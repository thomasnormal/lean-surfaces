import LeanModels.Go

/-!
# The multi-value rung: `add128`, and the carry a single-return model drops

Vendored verbatim from `crypto/internal/fips140/aes/ctr.go` (Go 1.25.6,
BSD-3-Clause, "Copyright 2009 The Go Authors", `docs/go-charter.md` §1.4):

    func add128(lo, hi uint64, x uint64) (uint64, uint64) {
        lo, c := bits.Add64(lo, x, 0)
        hi, _ = bits.Add64(hi, 0, c)
        return lo, hi
    }

## Why the census picked this function

Four lines that contain the entire rung and nothing else:

| line | what it exercises | corpus sites |
| --- | --- | ---: |
| `lo, c := …` | destructuring, `:=` form | 14,951 |
| `hi, _ = …` | destructuring, `=` form, **with a BLANK** | 7,364 / 7,964 |
| `return lo, hi` | multi-valued return | 13,991 |
| the signature | a function returning 2 | 5,733 |

It needs no named results, no naked `return`, no `panic`, no defined
types — every one of which `math/big`'s `addVV_g` would have dragged in.

It also exercises Go's **redeclaration** rule: `lo` is a PARAMETER, so
`lo, c := …` assigns `lo` and declares only `c`.

## The discriminator: a dropped carry passes 5 of 8 rows

`c` from the first `Add64` feeds the second. A model that returns only
the sum — the natural single-return shape — makes `c` zero forever:

| `⟨lo, hi, x⟩` | `gc` | carry-DROPPING model |
| --- | --- | --- |
| `⟨0, 0, 0⟩` | `⟨0, 0⟩` | `⟨0, 0⟩` — agrees |
| `⟨0, 0, 1⟩` | `⟨1, 0⟩` | `⟨1, 0⟩` — agrees |
| `⟨1, 2, 3⟩` | `⟨4, 2⟩` | `⟨4, 2⟩` — agrees |
| `⟨MAX, 0, 1⟩` | **`⟨0, 1⟩`** | `⟨0, 0⟩` — **FAILS** |
| `⟨MAX, 5, 1⟩` | **`⟨0, 6⟩`** | `⟨0, 5⟩` — **FAILS** |
| `⟨MAX, MAX, 1⟩` | **`⟨0, 0⟩`** | `⟨0, MAX⟩` — **FAILS** |
| `⟨MAX-1, 7, 1⟩` | `⟨MAX, 7⟩` | agrees |
| `⟨MAX, 0, 0⟩` | `⟨MAX, 0⟩` | agrees |

**Five of eight rows agree**, which is the whole point: a single-return
model is not obviously broken, it is quietly wrong exactly where carries
propagate. Only the three ripple rows separate them.

The last of those is worth its own note: at `⟨MAX, MAX, 1⟩` the second
`Add64` itself carries out, and that carry is **discarded by the blank
`_`**. Both models print `0` for `hi`, for opposite reasons — the correct
one because `MAX + 0 + 1` wrapped, the wrong one because it never added
the carry at all. It is the row where a blank target has to be a real
discard rather than an unbound name.

Every expected value was printed by the compiled function, never typed:

    $ cd <scratch>/mvgen && go build -o mvgen main.go && ./mvgen

with `go version go1.25.6 darwin/arm64`.
-/

namespace Examples.go.multivalue

open LeanModels LeanModels.Go

private def u64 (n : Int) : Expr := .lit (GoVal.mkInt IntKind.uint64 n)

/-- `MAX = 2^64 - 1` -/
private def MAX : Int := 18446744073709551615

/-! ## `add128`, transcribed statement for statement -/

def add128Body : List Stmt :=
  [ .assignCall [some "lo", some "c"] true
      (.callPkg "math/bits" "Add64" [.ident "lo", .ident "x", u64 0]),
    .assignCall [some "hi", none] false
      (.callPkg "math/bits" "Add64" [.ident "hi", u64 0, .ident "c"]),
    .ret [.ident "lo", .ident "hi"] ]

def prog : FuncTable := [("add128", ⟨["lo", "hi", "x"], false, add128Body⟩)]

private def emptyW : GoWorld := { store := [], nextAddr := 0, locals := [] }

private def run (lo hi x : Int) : Option (Int × Int) :=
  match (evalCallValues prog 256 (.call "add128" [u64 lo, u64 hi, u64 x])) emptyW with
  | .ok (.ok [.intV _ a, .intV _ b], _) => some (a, b)
  | _ => none

/-! ## The rows both models agree on — necessary, and NOT sufficient -/

#guard run 0 0 0 == some (0, 0)
#guard run 0 0 1 == some (1, 0)
#guard run 1 2 3 == some (4, 2)
#guard run (MAX - 1) 7 1 == some (MAX, 7)
#guard run MAX 0 0 == some (MAX, 0)

/-! ## THE RIPPLE ROWS — the carry crossing from `lo` into `hi`.

These are the only three of the eight that a carry-dropping model fails. -/

#guard run MAX 0 1 == some (0, 1)
#guard run MAX 5 1 == some (0, 6)
#guard run MAX MAX 1 == some (0, 0)

/-! ## The BLANK really discards.

`hi, _ = …` must not bind a variable named `_`, and the discarded value
must not reach anything. After the call the only locals are the
parameters and `c`. -/

-- The parameters must actually be BOUND, or the body refuses and a
-- fallback arm would pass this row without checking anything. The first
-- version of this guard did exactly that, and the non-vacuity flip caught
-- it: `| _ => true` swallowed the failing run (§G23).
private def boundW : GoWorld :=
  { store := [(0, GoVal.mkInt IntKind.uint64 MAX),
              (1, GoVal.mkInt IntKind.uint64 MAX),
              (2, GoVal.mkInt IntKind.uint64 1)],
    nextAddr := 3,
    locals := [("lo", 0), ("hi", 1), ("x", 2)] }

#guard (match (execSeq prog 256 add128Body) boundW with
        | .ok (.ok _, w) => (w.locals.find? (fun p => p.1 == "_")).isNone
        | _ => false) == true

/-! ...and the run this asserts about really does SUCCEED, so the row
above cannot pass by failing. -/
#guard (match (execSeq prog 256 add128Body) boundW with
        | .ok (.ok (Flow.returned [_, _]), _) => true
        | _ => false) == true

/-! ## Go has NO tuple values, and the model must not invent one.

`x := bits.Add64(1,2,0)` is a COMPILE error in Go — verified against
`gc`: "assignment mismatch: 1 variable but bits.Add64 returns 2 values".
So a two-valued call in a single-value context REFUSES; it must never
quietly yield the first result, which is precisely how a carry is lost. -/

#guard (match (evalExpr prog 64
                (.callPkg "math/bits" "Add64" [u64 1, u64 2, u64 0])) emptyW with
        | .error (.unsupported c m _) =>
            c.className == "unsupported"
              && m == "math/bits.Add64 returns 2 values in a single-value context"
        | _ => false) == true

/-! ## A count mismatch refuses in Go's own words, and never truncates. -/

#guard (match (execStmt prog 64
                (.assignCall [some "a", some "b", some "z"] true
                  (.callPkg "math/bits" "Add64" [u64 1, u64 2, u64 0]))) emptyW with
        | .error (.unsupported _ m _) =>
            m == "assignment mismatch: 3 variables but the call returns 2 values"
        | _ => false) == true

/-! ## Redeclaration: `lo, c := …` ASSIGNS the parameter `lo`.

Go's spec — "redeclaration does not introduce a new variable; it just
assigns a new value to the original". So after the first statement there
is exactly ONE binding for `lo`, not two. -/

#guard (match (evalCallValues prog 256
                (.call "add128" [u64 MAX, u64 0, u64 1])) emptyW with
        | .ok (.ok _, w) => (w.locals.filter (fun p => p.1 == "lo")).length ≤ 1
        | _ => false) == true

/-! ## Non-vacuity — these assert NEGATIVES. -/

#guard (run MAX 0 1).isSome
#guard (run MAX 0 1 != run MAX 0 0)            -- the carry MATTERS
#guard (run MAX 5 1 != some (0, 5))            -- NOT the dropped-carry answer
#guard (run MAX MAX 1 != some (0, MAX))        -- NOT the dropped-carry answer

end Examples.go.multivalue
