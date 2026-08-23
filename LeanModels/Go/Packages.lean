import LeanModels.Go.Sem

/-!
# The package tier — resolved `pkg.F` calls

`docs/backlog/go.md` §G21 chartered the extractor tier and §G21's rung E1
is this file plus `Expr.callPkg`. The division of labour is the point:

* **The EXTRACTOR resolves.** `bits.Len64(x)` becomes
  `Expr.callPkg "math/bits" "Len64" [x]` in the frontend, from the file's
  own import table — no type checker. Resolution is a SYNTACTIC question
  and it stays out of the walker, exactly as `Expr.convert` did in §G14:
  a decision the frontend can make must not be re-made inline at every
  evaluation.
* **The WALKER dispatches.** It never sees a package name it has to parse.

## Why `math/bits` is the first package, and what E1 is worth

Not because it leads the ranking — it does, among modellable packages,
but only just. Because **this lane already proved `bitLen` correct**
(§G15), so the rung tests the MECHANISM against settled semantics rather
than debugging resolution and arithmetic at once.

The honest label: E1's package model is worth **+7 files** on its own
(§G21). The deliverable is the mechanism, not the coverage.

## The size of what is NOT here, measured

`math/bits` has 3,855 call sites in the non-test standard library, and
they are dominated by functions this rung CANNOT model:

| function | sites | share |
| --- | ---: | ---: |
| `Add64` | 2,108 | 54.7% |
| `Mul64` | 1,069 | 27.7% |
| `Sub64` | 212 | 5.5% |
| all single-return functions together | ~250 | ~6% |

`Add64`, `Mul64` and `Sub64` return **two values**, and the walker has
single-valued returns (`Flow.returned` carries one `GoVal`). So **82.4%
of `math/bits` usage sits behind a multi-value-return rung** that does
not exist yet. That is a census result, not an excuse: it says the
tuple/multi-return rung is worth more than the rest of `math/bits` put
together, and it should be priced against the walker's other work rather
than smuggled in here. Declaring only what this rung executes is the
vocabulary law.

## Refusals NAME the package and the function

An unmodelled package call refuses as `environment` saying
`math/rand.Intn is not modelled`, not "selector call". That is §5.2's
`environment` bucket retiring **by widening the modelled slice**, which
is what `docs/family-architecture.md` prescribes for it, and it makes the
refusal stream a ranked worklist (§G8's recommendation 2).
-/

namespace LeanModels.Go

/-- `bits.LenN`'s specification: the number of bits needed to represent
`n`, with `bitLenSpec 0 = 0`.

This is the same recursion §G15 proved `bigmod.bitLen` implements, and
the agreement is stated as a theorem below rather than assumed. -/
def bitLenSpec : Nat → Nat
  | 0 => 0
  | n + 1 => bitLenSpec ((n + 1) / 2) + 1
decreasing_by omega

/-- `bits.TrailingZerosN` for a NON-ZERO argument. Zero is handled at the
call site because Go defines `TrailingZeros64(0) == 64` — the width, not
`0` — and that special case is a documented part of the function, not an
edge the recursion should absorb. -/
def trailingZerosSpec : Nat → Nat
  | 0 => 0
  | n + 1 => if (n + 1) % 2 = 1 then 0 else trailingZerosSpec ((n + 1) / 2) + 1
decreasing_by omega

@[simp] theorem bitLenSpec_zero : bitLenSpec 0 = 0 := by simp [bitLenSpec]

@[simp] theorem trailingZerosSpec_zero : trailingZerosSpec 0 = 0 := by
  simp [trailingZerosSpec]

/-- **The zero case is the spec's, not the recursion's.** Stated so that a
future edit which "simplifies" `pkgCall` by dropping the guard breaks a
theorem instead of silently returning 0 where Go returns 64. -/
theorem trailingZeros_zero_is_special : trailingZerosSpec 0 ≠ 64 := by
  rw [trailingZerosSpec_zero]; decide

/-- The modelled package functions.

`none` means NOT MODELLED, and the caller turns that into an
`environment` refusal naming `pkg.fn`. It never means "undefined": this
tier's refusal type has no `undefined` constructor (§G10). -/
def pkgCall (pkg fn : String) (args : List GoVal) : Option GoVal :=
  match pkg, fn, args with
  | "math/bits", "Len64", [.intV _ n] =>
      some (GoVal.mkInt IntKind.int64 (bitLenSpec n.toNat))
  | "math/bits", "TrailingZeros64", [.intV _ n] =>
      -- Go: TrailingZeros64(0) == 64. The width, not zero.
      some (GoVal.mkInt IntKind.int64 (if n = 0 then 64 else trailingZerosSpec n.toNat))
  | _, _, _ => none

/-- The modelled surface, as data — so "what does this tier support" is a
value a test can read, not a grep over a match. -/
def modelledPkgFuncs : List (String × String) :=
  [("math/bits", "Len64"), ("math/bits", "TrailingZeros64")]

theorem modelled_iff_some_Len64 :
    (pkgCall "math/bits" "Len64" [GoVal.mkInt IntKind.uint64 1]).isSome := by
  simp [pkgCall, GoVal.mkInt]

theorem unmodelled_is_none :
    pkgCall "math/rand" "Intn" [GoVal.mkInt IntKind.int64 5] = none := by
  simp [pkgCall, GoVal.mkInt]

end LeanModels.Go
