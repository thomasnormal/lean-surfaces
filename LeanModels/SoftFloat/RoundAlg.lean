/-
# SoftFloat, layer 2 — the ROUNDING ALGORITHM

THE INTERPRETER HALF of rounding.  `Round.lean` is the spec half and mentions
no algorithm at all; this file is the computable counterpart, and the two are
kept in separate files because that separation is the whole anti-circularity
argument (charter §3.5.2, `docs/statement-cookbook.md` §6).

WHY THE SPLIT MATTERS HERE SPECIFICALLY.  An `op_correct` of the form
`op fmt x y = roundQ fmt mode (exact …)` proved against THIS file would be
close to circular: any correct rounding algorithm is the same finite integer
computation core performs, so the equation would compare two spellings of one
procedure.  The escape is that `op_correct` is stated against `Round.lean`'s
`IsNearest`/`IsDirected` — which mention no procedure — and `roundQ` earns its
place by being proved to SATISFY them.  Until that proof is complete, `roundQ`
is an ALGORITHM WITH EVIDENCE, not a specification, and this file says so.

TERMINATION: none needed.  `Nat.log2`, a shift, a division, and two bounded
correction steps.  No search, no fuel, no well-founded recursion — so it is
kernel-reducible, which is what lets the rows below close by `decide`.
-/
import LeanModels.SoftFloat.Round

namespace LeanModels.SoftFloat

open Float.Model
open Float.Model.UnpackedFloat (Sign)

/-- `floor (log2 |q|)`, up to ±1 — a STARTING GUESS, corrected in `roundQ`. -/
def ilog2Q (q : Q) : Int := (Nat.log2 q.num.natAbs : Int) - (Nat.log2 q.den : Int)

/--
Split `|q| * 2 ^ (-e)` into quotient, remainder and divisor, all `Nat`.
No rational division and no ℝ: the scaling is a shift on one side or the other.
-/
def splitAt (q : Q) (e : Int) : Nat × Nat × Nat :=
  let a := q.num.natAbs
  let d := q.den
  let (N, D) := if e ≤ 0 then (a <<< (-e).toNat, d) else (a, d <<< e.toNat)
  (N / D, N % D, D)

/--
The rounding-direction attribute's decision on a significand, given the exact
residue `r / D`.  IEEE 754-2019 §4.3, and all five attributes are here — the
mode is a parameter, never a default.
-/
def RoundingMode.apply (mode : RoundingMode) (neg : Bool) (m r D : Nat) : Nat :=
  if r = 0 then m                                    -- exact: every mode agrees
  else
    match mode with
    | .towardZero      => m                          -- §4.3.2
    | .towardPositive  => if neg then m else m + 1   -- §4.3.2
    | .towardNegative  => if neg then m + 1 else m   -- §4.3.2
    | .nearestTiesToAway => if 2 * r ≥ D then m + 1 else m          -- §4.3.1
    | .nearestTiesToEven =>                                          -- §4.3.1
      if 2 * r > D then m + 1
      else if 2 * r < D then m
      else m + m % 2                                 -- the tie, to even

/--
Round an exact rational to `fmt` under `mode`, staying inside the spec algebra
(the result is a `Q`, so `IsNearest fmt q (roundQ fmt mode q)` is directly
statable).

Two bounded corrections, and each has a reason: the first fixes a `±1` error in
the `ilog2Q` guess, the second fixes a significand that the rounding step
carried past `2 ^ mantissaBits`.
-/
def roundQ (fmt : Format) (mode : RoundingMode) (q : Q) : Q :=
  if q.num = 0 then Q.ofInt 0
  else
    let neg := q.num < 0
    let e0 := max (ilog2Q q - (fmt.mantissaBits - 1 : Nat)) fmt.minExponent
    let e1 := if (splitAt q e0).1 ≥ 2 ^ fmt.mantissaBits then e0 + 1 else e0
    let e := max e1 fmt.minExponent
    let (m, r, D) := splitAt q e
    let m' := mode.apply neg m r D
    let (m'', e') := if m' ≥ 2 ^ fmt.mantissaBits then (m' / 2, e + 1) else (m', e)
    Q.dyadic (if neg then -(m'' : Int) else (m'' : Int)) e'

/-! ## What is PROVED -/

/-- Zero is representable at every format — `IsNearest`'s first field, base case. -/
theorem zero_repr (fmt : Format) : ReprQ fmt (Q.ofInt 0) := by
  refine ⟨0, fmt.minExponent, ?_, Int.le_refl _, ?_⟩
  · simpa using Nat.two_pow_pos fmt.mantissaBits
  · unfold Q.Eq Q.ofInt Q.dyadic
    split <;> simp

/-- `roundQ` sends zero to zero, at every format and every mode. -/
theorem roundQ_zero (fmt : Format) (mode : RoundingMode) (q : Q) (h : q.num = 0) :
    roundQ fmt mode q = Q.ofInt 0 := by
  unfold roundQ; rw [if_pos h]

/-- Hence `roundQ` satisfies `IsNearest` on zero, for any tie rule. -/
theorem roundQ_isNearest_zero (fmt : Format) (mode : RoundingMode) (q : Q)
    (h : q.num = 0) (tieOk : Q → Prop) (htie : tieOk (Q.ofInt 0)) :
    IsNearest fmt (Q.ofInt 0) (roundQ fmt mode q) tieOk := by
  rw [roundQ_zero fmt mode q h]
  exact nearest_of_exact fmt (Q.ofInt 0) tieOk (zero_repr fmt) htie

/-! ## What is OWED, named precisely rather than `sorry`ed

Two obligations remain before `roundQ` may be called a satisfying
implementation, and neither is a one-line gap:

* `roundQ_repr    : ∀ fmt mode q, ReprQ fmt (roundQ fmt mode q)`
  — the two correction steps exist to make this true; proving it means showing
    the corrected significand is below `2 ^ mantissaBits` and the exponent at
    or above `minExponent`.
* `roundQ_nearest : ∀ fmt q z, ReprQ fmt z →
                      Q.Le (Q.dist q (roundQ fmt .nearestTiesToEven q)) (Q.dist q z)`
  — the real content: nothing the format holds is strictly closer.  It needs
    the interleaving argument about representable values at differing
    exponents, which is the heart of a Flocq-style development.

They are stated here as text and NOT as `sorry`ed declarations on purpose: a
`sorry` would put `sorryAx` into this file's axiom prints and make every
neighbouring theorem's receipt unreadable (§0.1 II(a)).
-/

/-! ## EVIDENCE, in place of the missing proof — and labelled as evidence

`roundQ` was written independently of core's rounding.  Where the two must
agree they are checked to agree, at a 3-bit significand where every rounding
decision is forced and visible.  **This is corroboration, not proof**, and it
is what justifies carrying `roundQ` before the satisfaction theorems land.
-/

/-- A 3-bit significand: every rounding decision is forced and hand-checkable. -/
abbrev m3 : Format := { mantissaBitsWithoutImplicit := 2, exponentBits := 5 }
/-- IEEE 754-2019 §3.6 binary16, as an instance. -/
abbrev b16 : Format := { mantissaBitsWithoutImplicit := 10, exponentBits := 5 }

/-- Core's rounding of an exact dyadic, as a `Q`, for the agreement rows. -/
def coreRoundQ (fmt : Format) (m : Int) (e : Int) : Q :=
  match UnpackedFloat.normalize fmt m e .positive with
  | .finite s mm ee _ => Q.dyadic (s.apply mm) ee
  | _ => Q.ofInt 0

-- exactly representable values: rounding is the identity, at three widths
example : Q.beq (roundQ m3 .nearestTiesToEven (Q.dyadic 3 0)) (Q.dyadic 3 0) = true := by decide
example : Q.beq (roundQ b16 .nearestTiesToEven (Q.dyadic 1 (-1))) (Q.dyadic 1 (-1)) = true := by decide
#guard Q.beq (roundQ Format.binary64 .nearestTiesToEven (Q.dyadic 42 0)) (Q.dyadic 42 0)

-- AGREEMENT WITH CORE on the rounding-sensitive integers at a 3-bit significand
example : Q.beq (roundQ m3 .nearestTiesToEven (Q.ofInt 9))  (coreRoundQ m3 9 0)  = true := by decide
example : Q.beq (roundQ m3 .nearestTiesToEven (Q.ofInt 11)) (coreRoundQ m3 11 0) = true := by decide
example : Q.beq (roundQ m3 .nearestTiesToEven (Q.ofInt 13)) (coreRoundQ m3 13 0) = true := by decide
example : Q.beq (roundQ m3 .nearestTiesToEven (Q.ofInt 5))  (coreRoundQ m3 5 0)  = true := by decide
example : Q.beq (roundQ m3 .nearestTiesToEven (Q.ofInt 7))  (coreRoundQ m3 7 0)  = true := by decide

-- THE MODES GENUINELY DIFFER, so the parameter is not decoration.
-- 9 = 1001b needs four bits; at three, ties-to-even and toward-zero give 8,
-- toward-positive gives 10.
example : (roundQ m3 .nearestTiesToEven (Q.ofInt 9)).num = 8 := by decide
example : (roundQ m3 .towardZero (Q.ofInt 9)).num = 8 := by decide
example : (roundQ m3 .towardPositive (Q.ofInt 9)).num = 10 := by decide

#print axioms zero_repr
#print axioms roundQ_zero
#print axioms roundQ_isNearest_zero

end LeanModels.SoftFloat
