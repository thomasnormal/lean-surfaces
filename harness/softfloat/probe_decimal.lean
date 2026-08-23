/-
SOFTFLOAT PLAN STEP 3 — FEASIBILITY PROBE for correctly-rounded
shortest-round-trip decimal printing.

WHY THIS IS NOW THE ONLY BLOCKING ITEM.  The consumer-site census
(`docs/softfloat-consumer-census.json`) found ZERO unrouted opaque crossings:
ES's integer arm is routed through `.toModel`, so the transfer layer has no
consumer waiting.  What remains is a REAL ALGORITHM, not a routing — core
ships no decimal printer at all (`Float.toString` is `opaque`).

THE TERMINATION QUESTION, and it is the point of this probe.  Layer 2's answer
to "fuel or not" was NONE: every function is a composition of total Int/Nat
operations that do not SEARCH (charter §3.4).  Shortest-round-trip printing is
the first SoftFloat function that genuinely searches — it tries digit counts
until one round-trips.  So it needs well-founded recursion or fuel, AND
WELL-FOUNDED RECURSION IS EXACTLY WHAT COST US `sqrt`: `Nat.sqrt`'s
`termination_by` is why `sqrt` closes under neither `rfl` nor `decide`
(charter §1.2).  Hence FUEL, and this probe checks the fuel shape reduces.

Expected: ZERO errors.
RUN:  tools/check.sh harness/softfloat/probe_decimal.lean
-/
import Init.Data.Float.Model

open Float.Model

/-! ## The rounding interval, in exact integer arithmetic -/

/--
A finite float `v` owns the reals that round to it.  A decimal ROUND-TRIPS iff
it lies in that interval.  Everything is kept over one common denominator so
the test is integer comparison — ℝ never appears, which is charter §3.5.1's
whole tractability argument.
-/
structure Interval where
  /-- Scaled low endpoint. -/
  lo : Int
  /-- Scaled value. -/
  val : Int
  /-- Scaled high endpoint. -/
  hi : Int
  /-- The common (positive) denominator. -/
  den : Nat
deriving Repr

/-- `10 ^ n`, total. -/
abbrev p10 (n : Nat) : Nat := 10 ^ n

/--
Does the `n`-digit decimal nearest `val/den` land back inside `(lo/den, hi/den)`?

`D` is that decimal's numerator over `10^n`.  Round-trip is
`lo/den < D/10^n < hi/den`, and cross-multiplying by the positive `den` and
`10^n` leaves TWO INTEGER COMPARISONS and nothing else.
-/
def roundTripsAt (I : Interval) (n : Nat) : Bool :=
  let s : Int := (p10 n : Int)
  let D : Int := (I.val * s + (I.den : Int) / 2) / (I.den : Int)
  I.lo * s < D * (I.den : Int) && D * (I.den : Int) < I.hi * s

/--
THE SEARCH, FUEL-SHAPED.  Try `n = 0, 1, 2, …` and stop at the first that
round-trips.  Fuel is a PARAMETER (`docs/statement-cookbook.md` §5), never a
numeral in a hypothesis, and exhaustion answers `none` — LOUD, never a guess.
-/
def shortestDigits (I : Interval) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, n => if roundTripsAt I n then some n else shortestDigits I fuel (n + 1)

/-! ## FLAGGED, not absorbed: `/` on `Int` is a CONVENTION CHOICE

The nearest-decimal step divides, and `Int.ediv`, `Int.tdiv` and `Int.fdiv`
disagree on negatives.  The sample below is positive, where all three agree; a
real implementation must PIN the convention and say which, because a printer
that picks one silently is the same shape of defect one level down.  Recorded
so step 3 starts with it rather than discovering it.
-/

/-- `(lo, val, hi, den) = (1, 2, 3, 10)` — the interval `(0.1, 0.3)` around `0.2`.
    `n = 0`: `D = 0`, and `1*1 < 0*10` is false, so zero digits does NOT round-trip.
    `n = 1`: `D = 2`, and `1*10 < 2*10 < 3*10` holds, so the answer is 1 digit. -/
abbrev sample : Interval := ⟨1, 2, 3, 10⟩

/-! ## It reduces — `rfl` AND `decide`, which is the whole question -/

#guard roundTripsAt sample 0 == false
#guard roundTripsAt sample 1 == true
example : roundTripsAt sample 0 = false := rfl
example : roundTripsAt sample 1 = true := rfl

#guard shortestDigits sample 20 0 == some 1
example : shortestDigits sample 20 0 = some 1 := rfl
example : shortestDigits sample 20 0 = some 1 := by decide

-- fuel exhaustion is REACHABLE and answers `none`, never a wrong digit count
example : shortestDigits sample 0 0 = none := rfl

/-! ## The inputs it needs are already kernel-reducible -/

example : (Float.Model.ofNat 3).unpack.isFinite = true := rfl
example : ((0.5 : Float).toModel.unpack).isFinite = true := rfl
-- big-Nat arithmetic at binary64 scale, which the digit loop lives on
example : Nat.log2 (2 ^ 52) = 52 := by decide
example : (2 ^ 52 : Nat) * 10 ^ 17 > 0 := by decide

/-! ## The `sqrt` contrast, which is WHY the loop is fuelled and not well-founded -/

#guard Nat.sqrt 49 == 7        -- untrusted evaluator: fine
-- `example : Nat.sqrt 49 = 7 := rfl` would FAIL — see probe_walls.lean.
-- The fuelled loop above closes by `rfl` and by `decide`.  That is the choice.

theorem decimal_search_reduces : shortestDigits sample 20 0 = some 1 := rfl
theorem fuel_exhaustion_is_none : shortestDigits sample 0 0 = none := rfl

#print axioms decimal_search_reduces
#print axioms fuel_exhaustion_is_none
