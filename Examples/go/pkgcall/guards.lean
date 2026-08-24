import LeanModels.Go

/-!
# Rung E1's acceptance: `log64` and `ntz64` through a RESOLVED package call

`docs/backlog/go.md` §G21 chartered the extractor tier and sized E1 as
`pkg.F` resolution plus one package end to end. This is the walker half's
acceptance; the resolver half's is
`harness/go/construct_census.go --resolve` (10 rows, two-sided).

Vendored verbatim from `cmd/compile/internal/ssa/rewrite.go` (Go 1.25.6,
BSD-3-Clause, "Copyright 2009 The Go Authors", `docs/go-charter.md` §1.4):

    func log64(n int64) int64 { return int64(bits.Len64(uint64(n))) - 1 }
    func ntz64(x int64) int   { return bits.TrailingZeros64(uint64(x)) }

## Why these two, and why they can fail

`math/bits` is the first package because this lane **already proved
`bitLen` correct** (§G15) — E1 tests the MECHANISM (resolve, dispatch,
cross a package boundary) against semantics already settled, rather than
debugging both at once.

Two functions rather than one, because a dispatch table with a single
entry is indistinguishable from a hard-coded answer.

The discriminating arguments are the NEGATIVE ones. `uint64(n)` on a
negative `int64` wraps to a huge value, so:

| call | `gc` | what a wrong model does |
| --- | ---: | --- |
| `log64(-1)` | **63** | no wrap -> nonsense; `Len64` of `-1` is not a Nat |
| `log64(0)` | **-1** | `Len64(0) = 0`, then `- 1`; a model that special-cased 0 to 1 gives 0 |
| `ntz64(0)` | **64** | Go DEFINES this as the width; the recursion alone gives 0 |
| `ntz64(-1)` | **0** | the wrapped value is all-ones |
| `ntz64(MinInt64)` | **63** | the single set bit is the top one |

`ntz64(0) = 64` and `log64(0) = -1` pull in opposite directions on the
same zero argument, which is why both functions are here.

Every expected value was printed by the compiled functions, never typed:

    $ cd <scratch>/e1gen && go build -o e1gen main.go && ./e1gen

with `go version go1.25.6 darwin/arm64`.
-/

namespace Examples.go.pkgcall

open LeanModels LeanModels.Go

private def i64 (n : Int) : Expr := .lit (GoVal.mkInt IntKind.int64 n)

/-! ## The two functions, transcribed statement for statement.

`bits.Len64(…)` is `Expr.callPkg "math/bits" "Len64" […]` — the EXTRACTOR
resolved the selector from the import table; the walker never sees the
name `bits`. -/

def log64Body : List Stmt :=
  [ .ret [(.binary .sub
      (.convert "int64" (.callPkg "math/bits" "Len64" [.convert "uint64" (.ident "n")]))
      (i64 1))] ]

def ntz64Body : List Stmt :=
  [ .ret [(.callPkg "math/bits" "TrailingZeros64" [.convert "uint64" (.ident "x")])] ]

def prog : FuncTable :=
  [ ("log64", ⟨["n"], log64Body⟩), ("ntz64", ⟨["x"], ntz64Body⟩) ]

private def emptyW : GoWorld := { store := [], nextAddr := 0, locals := [] }

private def run (fn : String) (n : Int) : Option Int :=
  match (callFunction prog 256 fn [GoVal.mkInt IntKind.int64 n]) emptyW with
  | .ok (.ok (.intV _ v), _) => some v
  | _ => none

/-! ## `log64` against `gc` -/

#guard run "log64" 0 == some (-1)
#guard run "log64" 1 == some 0
#guard run "log64" 2 == some 1
#guard run "log64" 3 == some 1
#guard run "log64" 8 == some 3
#guard run "log64" 255 == some 7
#guard run "log64" 256 == some 8
#guard run "log64" (-1) == some 63
#guard run "log64" (-2) == some 63
#guard run "log64" (-8) == some 63
#guard run "log64" 9223372036854775807 == some 62
#guard run "log64" (-9223372036854775808) == some 63

/-! ## `ntz64` against `gc` -/

#guard run "ntz64" 0 == some 64
#guard run "ntz64" 1 == some 0
#guard run "ntz64" 2 == some 1
#guard run "ntz64" 3 == some 0
#guard run "ntz64" 8 == some 3
#guard run "ntz64" 255 == some 0
#guard run "ntz64" 256 == some 8
#guard run "ntz64" (-1) == some 0
#guard run "ntz64" (-2) == some 1
#guard run "ntz64" (-8) == some 3
#guard run "ntz64" 9223372036854775807 == some 0
#guard run "ntz64" (-9223372036854775808) == some 63

/-! ## The package model agrees with the PROVED spec.

§G15 proved `bigmod.bitLen` computes `bitLenSpec`. `bits.Len64` is
modelled by the same `bitLenSpec`, so the package model and the proved
function are the same function — stated here rather than assumed. -/

#guard (match pkgCall "math/bits" "Len64" [GoVal.mkInt IntKind.uint64 255] with
        | .values [.intV _ v] => v == (bitLenSpec 255 : Nat)
        | _ => false) == true

#guard (match pkgCall "math/bits" "Len64" [GoVal.mkInt IntKind.uint64 0] with
        | .values [.intV _ v] => v == 0        -- gc: Len64(0) = 0
        | _ => false) == true

/-- The spec half, stated about the spec alone so it is a THEOREM and not
an evaluation: `Len64`'s model is the same recursion §G15 proved
`bigmod.bitLen` implements, so the two cannot drift apart silently.

The `uint64.wrap` is not noise: `Len64`'s PARAMETER is `uint64`, so §G24
normalises every argument through that kind rather than trusting the
caller's `IntKind`. Without it a negative `int64` would reach `bitLenSpec`
through `Int.toNat` and silently read as 0. -/
theorem len64_model_is_the_proved_spec (k : IntKind) (v : Int) :
    pkgCall "math/bits" "Len64" [.intV k v]
      = .values [GoVal.mkInt IntKind.int64
                  (bitLenSpec (IntKind.uint64.wrap v).toNat)] := by
  rfl

/-! ## An UNMODELLED package refuses as `environment`, NAMING the callee.

This is §5.2's `environment` bucket retiring by widening the modelled
slice — and a refusal that names `pkg.fn` makes the refusal stream a
ranked worklist (§G8's recommendation 2) rather than noise. -/

#guard (match (evalExpr prog 64 (.callPkg "math/rand" "Intn" [i64 5])) emptyW with
        | .error (.unsupported c m _) =>
            c.className == "environment" && m == "math/rand.Intn is not modelled"
        | _ => false) == true

/-! ...and it is never `undefined` — this tier's refusal type has no such
constructor (§G10), so the zero-UB gate holds across a package boundary. -/

#guard (match (evalExpr prog 64 (.callPkg "math/rand" "Intn" [i64 5])) emptyW with
        | .error (.unsupported c _ _) => c.className != "undefined"
        | _ => false) == true

/-! ## Non-vacuity — these assert NEGATIVES. -/

#guard (run "log64" (-1)).isSome
#guard (run "log64" (-1) != run "log64" 1)          -- the wrap MATTERS
#guard (run "ntz64" 0 != run "log64" 0)             -- 64 vs -1 on the same argument
#guard (run "ntz64" 0 != some 0)                    -- NOT the bare recursion's answer

end Examples.go.pkgcall
