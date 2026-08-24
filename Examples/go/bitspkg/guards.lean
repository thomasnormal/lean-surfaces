import LeanModels.Go

/-!
# The `math/bits` completion rung: eight functions, one constant

`docs/backlog/go.md` §G23 priced this rung **in advance at +7 files** and
listed every blocker. This is that rung: the eight remaining functions
plus `UintSize`, which is not a function at all.

## The constant is a different KIND, not a nullary function

`const UintSize = uintSize`. Go distinguishes it from a call —
`bits.UintSize()` does not compile — so it gets its own node
(`Expr.pkgConst`) and its own extractor rule. Modelling it as a
zero-argument `callPkg` would let the model accept a program `gc`
rejects, which is the test §G23 used to rule out tuple values.

## `Div` PANICS, and a panic is not a gap

`bits.Div` panics on a zero divisor and on a quotient that will not fit.
That forced `pkgCall`'s result to widen from `Option` to `PkgOutcome`
with three cases, because folding a **defined panic** into "not modelled"
would report the program's own behaviour as a limit of this tier — the
§5.2 mis-bucketing §G14 already paid for once.

## Vendored acceptance

From `math/big/arith.go` — one of the seven files this rung is meant to
unblock (Go 1.25.6, BSD-3-Clause, "Copyright 2009 The Go Authors"):

    func mulAddWWW_g(x, y, c Word) (z1, z0 Word) {
        hi, lo := bits.Mul(uint(x), uint(y))
        var cc uint
        lo, cc = bits.Add(lo, uint(c), 0)
        return Word(hi + cc), Word(lo)
    }

`Word` is `uintptr`, 64-bit here; the frontend emits its conversions as
`uint64`, which is sound for arithmetic and loses only type identity (no
methods at this rung).

The discriminator is `hi + cc`: the carry out of `Add` is **folded into
the high word**. At `⟨MAX, MAX, MAX⟩` `gc` returns `⟨MAX, 0⟩`, and a
model that dropped that carry returns `⟨MAX-1, 0⟩` — the same low word,
one less high word.

Every expected value was printed by the compiled functions, never typed:

    $ cd <scratch>/b8 && go build -o b8 main.go && ./b8

with `go version go1.25.6 darwin/arm64`.
-/

namespace Examples.go.bitspkg

open LeanModels LeanModels.Go

private def MAX : Int := 18446744073709551615
private def MAXm1 : Int := 18446744073709551614
private def u (n : Int) : GoVal := GoVal.mkInt IntKind.uint64 n
private def ue (n : Int) : Expr := .lit (u n)

private def two (pkg fn : String) (as : List Int) : Option (Int × Int) :=
  match pkgCall pkg fn (as.map u) with
  | .values [.intV _ a, .intV _ b] => some (a, b)
  | _ => none

private def one (pkg fn : String) (as : List Int) : Option Int :=
  match pkgCall pkg fn (as.map u) with
  | .values [.intV _ a] => some a
  | _ => none

/-! ## `Mul64` / `Mul` — the full 128-bit product -/

#guard two "math/bits" "Mul64" [0, 0] == some (0, 0)
#guard two "math/bits" "Mul64" [1, 1] == some (0, 1)
#guard two "math/bits" "Mul64" [2, 3] == some (0, 6)
#guard two "math/bits" "Mul64" [MAX, 2] == some (1, MAXm1)
#guard two "math/bits" "Mul64" [MAX, MAX] == some (MAXm1, 1)
#guard two "math/bits" "Mul64" [4294967296, 4294967296] == some (1, 0)
#guard two "math/bits" "Mul" [MAX, 2] == some (1, MAXm1)

/-! ## `Sub64` / `Sub` — the BORROW is the second value -/

#guard two "math/bits" "Sub64" [5, 3, 0] == some (2, 0)
#guard two "math/bits" "Sub64" [3, 5, 0] == some (MAXm1, 1)
#guard two "math/bits" "Sub64" [0, 0, 1] == some (MAX, 1)
#guard two "math/bits" "Sub64" [0, 1, 0] == some (MAX, 1)
#guard two "math/bits" "Sub64" [MAX, MAX, 1] == some (MAX, 1)
#guard two "math/bits" "Sub64" [5, 3, 1] == some (1, 0)
#guard two "math/bits" "Sub" [3, 5, 0] == some (MAXm1, 1)

/-! ## `Add` at `uint` width — the same function as `Add64` here -/

#guard two "math/bits" "Add" [1, 2, 0] == some (3, 0)
#guard two "math/bits" "Add" [MAX, 1, 0] == some (0, 1)
#guard two "math/bits" "Add" [MAX, 0, 1] == some (0, 1)

/-! ## `LeadingZeros` / `TrailingZeros`, and their ZERO cases.

Both return the WIDTH at zero, not 0. `LeadingZeros(0) = 64` because
`Len(0) = 0`; `TrailingZeros(0) = 64` by definition. -/

#guard one "math/bits" "LeadingZeros" [0] == some 64
#guard one "math/bits" "LeadingZeros" [1] == some 63
#guard one "math/bits" "LeadingZeros" [2] == some 62
#guard one "math/bits" "LeadingZeros" [255] == some 56
#guard one "math/bits" "LeadingZeros" [MAX] == some 0
#guard one "math/bits" "TrailingZeros" [0] == some 64
#guard one "math/bits" "TrailingZeros" [1] == some 0
#guard one "math/bits" "TrailingZeros" [2] == some 1
#guard one "math/bits" "TrailingZeros" [255] == some 0
#guard one "math/bits" "TrailingZeros" [MAX] == some 0

/-! ## `Div` — the quotient, and its two DEFINED panics -/

#guard two "math/bits" "Div" [0, 10, 3] == some (3, 1)
#guard two "math/bits" "Div" [0, 100, 7] == some (14, 2)
#guard two "math/bits" "Div" [1, 0, 2] == some (9223372036854775808, 0)

#guard (match pkgCall "math/bits" "Div" [u 0, u 5, u 0] with
        | .panics m => m == "runtime error: integer divide by zero"
        | _ => false) == true
#guard (match pkgCall "math/bits" "Div" [u 5, u 0, u 3] with
        | .panics m => m == "runtime error: integer overflow"
        | _ => false) == true

/-! ...and a PANIC is not a GAP. An unmodelled function is
`notModelled`; a defined panic is `panics`; conflating them would report
the program's behaviour as this tier's limit. -/

#guard (match pkgCall "math/rand" "Intn" [u 5] with
        | .notModelled => true | _ => false) == true

/-! ## The CONSTANT -/

-- matched structurally: `GoVal` has no `BEq` (§G15 — a nested `List`
-- makes `DecidableEq` underivable), so equality is read off the fields.
#guard (match pkgConst "math/bits" "UintSize" with
        | some (.intV _ n) => n == 64 | _ => false) == true
#guard (match pkgConst "math/bits" "NoSuchConst" with
        | none => true | _ => false) == true

private def emptyW : GoWorld := { store := [], nextAddr := 0, locals := [] }

#guard (match (evalExpr [] 8 (.pkgConst "math/bits" "UintSize")) emptyW with
        | .ok (.ok (.intV _ n), _) => n == 64 | _ => false) == true

/-! ...and an unmodelled constant refuses as `environment`, naming it. -/

#guard (match (evalExpr [] 8 (.pkgConst "math/rand" "Seed")) emptyW with
        | .error (.unsupported c m _) =>
            c.className == "environment" && m == "math/rand.Seed is not modelled"
        | _ => false) == true

/-! ## THE VENDORED CHAIN: `mulAddWWW_g` -/

def mulAddBody : List Stmt :=
  [ .assignCall [some "hi", some "lo"] true
      (.callPkg "math/bits" "Mul"
        [.convert "uint64" (.ident "x"), .convert "uint64" (.ident "y")]),
    .declare "cc" (ue 0),
    .assignCall [some "lo", some "cc"] false
      (.callPkg "math/bits" "Add"
        [.ident "lo", .convert "uint64" (.ident "c"), ue 0]),
    .ret [ .convert "uint64" (.binary .add (.ident "hi") (.ident "cc")),
           .convert "uint64" (.ident "lo") ] ]

def prog : FuncTable := [("mulAddWWW_g", ⟨["x", "y", "c"], false, mulAddBody⟩)]

private def runMul (x y c : Int) : Option (Int × Int) :=
  match (evalCallValues prog 256 (.call "mulAddWWW_g" [ue x, ue y, ue c])) emptyW with
  | .ok (.ok [.intV _ a, .intV _ b], _) => some (a, b)
  | _ => none

#guard runMul 0 0 0 == some (0, 0)
#guard runMul 2 3 4 == some (0, 10)
#guard runMul MAX MAX 0 == some (MAXm1, 1)
#guard runMul MAX 1 1 == some (1, 0)
#guard runMul 4294967296 4294967296 0 == some (1, 0)
#guard runMul MAX 2 MAX == some (2, 18446744073709551613)
#guard runMul 0 0 MAX == some (0, MAX)

/-! **The carry-into-the-high-word row.** `gc` says `⟨MAX, 0⟩`; a model
that dropped `Add`'s carry says `⟨MAX-1, 0⟩` — same low word, one less
high word. -/

#guard runMul MAX MAX MAX == some (MAX, 0)

/-! ## Non-vacuity — these assert NEGATIVES. -/

#guard (runMul MAX MAX MAX).isSome
#guard (runMul MAX MAX MAX != some (MAXm1, 0))     -- NOT the dropped-carry answer
#guard (runMul MAX MAX MAX != runMul MAX MAX 0)    -- the third argument MATTERS
#guard (one "math/bits" "LeadingZeros" [0] != some 0)   -- the WIDTH, not zero
#guard (two "math/bits" "Sub64" [3, 5, 0] != some (MAXm1, 0))  -- the borrow is set

end Examples.go.bitspkg
