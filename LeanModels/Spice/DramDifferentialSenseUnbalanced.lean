import LeanModels.Spice.DramDifferentialSense

/-!
# Unbalanced differential-sense trajectories

The balanced reduction is useful for closed-form gain and global
determinacy, but a physical single-ended DRAM charge-sharing phase does not
place the two latch nodes on the exact `vtrue + vcomplement = VDD` manifold.
This module constructs the full two-coordinate trajectory instead.

The proof field below clamps voltages only outside the source model's
0--5 V validity square. Inside that square it is definitionally tied to the
same four MOS1 currents and two capacitor KCL equations as
`dramDifferentialSenseDAE`. A barrier proof must therefore establish that the
constructed trajectory never uses the extension before it can be exposed as
a physical behavior.
-/

namespace LeanModels.Spice

open LeanModels.Circuit

open Set

/-- Square of the positive part, with an upper clamp used only to obtain a
global Lipschitz extension. On every MOS1 overdrive occurring in the 0--5 V
rail square, the upper clamp is inactive. -/
noncomputable def dramSenseReluSquare (value : ℝ) : ℝ :=
  (Set.projIcc (0 : ℝ) 4 (by norm_num) value : ℝ) ^ 2

theorem dramSenseReluSquare_nonnegative (value : ℝ) :
    0 ≤ dramSenseReluSquare value := by
  exact sq_nonneg _

theorem dramSenseReluSquare_proj_bounds (value : ℝ) :
    0 ≤ (Set.projIcc (0 : ℝ) 4 (by norm_num) value : ℝ) ∧
      (Set.projIcc (0 : ℝ) 4 (by norm_num) value : ℝ) ≤ 4 :=
  (Set.projIcc (0 : ℝ) 4 (by norm_num) value).property

/-- The clamped positive-part square is globally Lipschitz. -/
theorem dramSenseReluSquare_lipschitz :
    LipschitzWith (8 : NNReal) dramSenseReluSquare := by
  apply LipschitzWith.of_dist_le_mul
  intro left right
  let pleft : ℝ :=
    Set.projIcc (0 : ℝ) 4 (by norm_num) left
  let pright : ℝ :=
    Set.projIcc (0 : ℝ) 4 (by norm_num) right
  have hprojection :
      dist pleft pright ≤ dist left right := by
    simpa only [pleft, pright, Subtype.dist_eq, NNReal.coe_one,
      one_mul] using
      ((LipschitzWith.projIcc
        (show (0 : ℝ) ≤ 4 by norm_num)).dist_le_mul left right)
  have hsum : |pleft + pright| ≤ 8 := by
    rw [abs_of_nonneg
      (add_nonneg
        (Set.projIcc (0 : ℝ) 4 (by norm_num) left).property.1
        (Set.projIcc (0 : ℝ) 4 (by norm_num) right).property.1)]
    linarith [
      (Set.projIcc (0 : ℝ) 4 (by norm_num) left).property.2,
      (Set.projIcc (0 : ℝ) 4 (by norm_num) right).property.2]
  rw [Real.dist_eq, dramSenseReluSquare, dramSenseReluSquare]
  change |pleft ^ 2 - pright ^ 2| ≤ (8 : ℝ) * |left - right|
  rw [sq_sub_sq, abs_mul]
  exact mul_le_mul hsum hprojection (abs_nonneg _) (by norm_num)

/-- Within its upper validity bound, the proof field is exactly the square
of the ordinary positive part. -/
theorem dramSenseReluSquare_eq_max_sq
    {value : ℝ} (hupper : value ≤ 4) :
    dramSenseReluSquare value = (max value 0) ^ 2 := by
  unfold dramSenseReluSquare
  by_cases hnonpositive : value ≤ 0
  · rw [Set.projIcc_of_le_left (by norm_num) hnonpositive,
      max_eq_right hnonpositive]
  · have hnonnegative : 0 ≤ value := le_of_not_ge hnonpositive
    rw [Set.projIcc_of_mem (by norm_num) ⟨hnonnegative, hupper⟩,
      max_eq_left hnonnegative]

/-- Zero-channel-length-modulation MOS1 current written as a difference of
two positive-part squares. This representation exposes the regularity needed
for the ODE construction without changing the primitive device law. -/
theorem mos1ForwardCurrent_zero_lambda_eq_max_sq
    (polarity : MosPolarity) (threshold beta vgs vds : ℝ)
    (hvds : 0 ≤ vds) :
    mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 } vgs vds =
      beta / 2 *
        ((max (vgs - threshold) 0) ^ 2 -
          (max (vgs - threshold - vds) 0) ^ 2) := by
  unfold mos1ForwardCurrent
  by_cases hcutoff : vgs ≤ threshold
  · rw [if_pos hcutoff]
    have hoverdrive : vgs - threshold ≤ 0 := by linarith
    have hremaining : vgs - threshold - vds ≤ 0 := by linarith
    rw [max_eq_right hoverdrive, max_eq_right hremaining]
    ring
  · rw [if_neg hcutoff]
    have hoverdrive : 0 ≤ vgs - threshold := by linarith
    rw [max_eq_left hoverdrive]
    by_cases htriode : vds ≤ vgs - threshold
    · rw [if_pos htriode]
      have hremaining : 0 ≤ vgs - threshold - vds := by linarith
      rw [max_eq_left hremaining]
      ring
    · rw [if_neg htriode]
      have hremaining : vgs - threshold - vds ≤ 0 := by linarith
      rw [max_eq_right hremaining]
      ring

/-- Nominal NMOS current extended smoothly enough for global ODE existence.
Its arguments will be clamped node voltages in the vector field below. -/
noncomputable def dramDifferentialSenseClampedNCurrent
    (gate output : ℝ) : ℝ :=
  (1 / 20000 : ℝ) *
    (dramSenseReluSquare (gate - 1) -
      dramSenseReluSquare (gate - 1 - output))

theorem dramDifferentialSenseClampedNCurrent_eq_nominal
    {gate output : ℝ}
    (hgateUpper : gate ≤ 5)
    (houtput0 : 0 ≤ output) :
    dramDifferentialSenseClampedNCurrent gate output =
      dramDifferentialSenseNCurrent
        nominalDramDifferentialSenseInstance gate output := by
  unfold dramDifferentialSenseClampedNCurrent
    dramDifferentialSenseNCurrent
    nominalDramDifferentialSenseInstance
  rw [mos1ForwardCurrent_zero_lambda_eq_max_sq .nmos
    1 (1 / 10000) gate output houtput0]
  rw [dramSenseReluSquare_eq_max_sq (by linarith),
    dramSenseReluSquare_eq_max_sq (by linarith)]
  ring

/-- Rail projection used by the proof extension. -/
noncomputable def dramSenseVoltageClamp (value : ℝ) : ℝ :=
  Set.projIcc (0 : ℝ) 5 (by norm_num) value

theorem dramSenseVoltageClamp_lipschitz :
    LipschitzWith (1 : NNReal) dramSenseVoltageClamp := by
  apply LipschitzWith.of_dist_le_mul
  intro left right
  simpa only [dramSenseVoltageClamp, Subtype.dist_eq,
    NNReal.coe_one, one_mul] using
    ((LipschitzWith.projIcc
      (show (0 : ℝ) ≤ 5 by norm_num)).dist_le_mul left right)

@[simp]
theorem dramSenseVoltageClamp_eq
    {value : ℝ} (hlower : 0 ≤ value) (hupper : value ≤ 5) :
    dramSenseVoltageClamp value = value := by
  exact congrArg Subtype.val
    (Set.projIcc_of_mem (by norm_num) ⟨hlower, hupper⟩)

/-- The nominal extended NMOS current is deliberately given a very loose
global Lipschitz constant. The quantitative value is not used as a gain
claim; it only provides a constructive finite-horizon ODE witness. -/
theorem dramDifferentialSenseClampedNCurrent_lipschitz :
    LipschitzWith (1 : NNReal)
      (Function.uncurry dramDifferentialSenseClampedNCurrent) := by
  apply LipschitzWith.of_dist_le_mul
  rintro ⟨gate₁, output₁⟩ ⟨gate₂, output₂⟩
  let totalDistance : ℝ :=
    dist (gate₁, output₁) (gate₂, output₂)
  have hgate :
      |gate₁ - gate₂| ≤ totalDistance := by
    dsimp [totalDistance]
    rw [Prod.dist_eq, Real.dist_eq]
    exact le_max_left _ _
  have houtput :
      |output₁ - output₂| ≤ totalDistance := by
    dsimp [totalDistance]
    rw [Prod.dist_eq, Real.dist_eq]
    exact le_max_right _ _
  have hfirst :=
    dramSenseReluSquare_lipschitz.dist_le_mul
      (gate₁ - 1) (gate₂ - 1)
  have hsecond :=
    dramSenseReluSquare_lipschitz.dist_le_mul
      (gate₁ - 1 - output₁) (gate₂ - 1 - output₂)
  rw [Real.dist_eq] at hfirst hsecond
  have hfirstBound :
      |dramSenseReluSquare (gate₁ - 1) -
          dramSenseReluSquare (gate₂ - 1)| ≤
        8 * totalDistance := by
    calc
      _ ≤ 8 * |(gate₁ - 1) - (gate₂ - 1)| := hfirst
      _ = 8 * |gate₁ - gate₂| := by ring_nf
      _ ≤ 8 * totalDistance := by gcongr
  have hargument :
      |(gate₁ - 1 - output₁) -
          (gate₂ - 1 - output₂)| ≤
        2 * totalDistance := by
    calc
      _ = |(gate₁ - gate₂) - (output₁ - output₂)| := by ring_nf
      _ ≤ |gate₁ - gate₂| + |output₁ - output₂| :=
        abs_sub _ _
      _ ≤ 2 * totalDistance := by linarith
  have hsecondBound :
      |dramSenseReluSquare (gate₁ - 1 - output₁) -
          dramSenseReluSquare (gate₂ - 1 - output₂)| ≤
        16 * totalDistance := by
    calc
      _ ≤ 8 *
          |(gate₁ - 1 - output₁) -
            (gate₂ - 1 - output₂)| := hsecond
      _ ≤ 8 * (2 * totalDistance) := by gcongr
      _ = 16 * totalDistance := by ring
  have hdistanceNonnegative : 0 ≤ totalDistance := dist_nonneg
  rw [Real.dist_eq]
  change
    |(1 / 20000 : ℝ) *
          (dramSenseReluSquare (gate₁ - 1) -
            dramSenseReluSquare (gate₁ - 1 - output₁)) -
        (1 / 20000 : ℝ) *
          (dramSenseReluSquare (gate₂ - 1) -
            dramSenseReluSquare (gate₂ - 1 - output₂))| ≤
      (1 : ℝ) * totalDistance
  have hcombined :
      |(dramSenseReluSquare (gate₁ - 1) -
            dramSenseReluSquare (gate₁ - 1 - output₁)) -
          (dramSenseReluSquare (gate₂ - 1) -
            dramSenseReluSquare (gate₂ - 1 - output₂))| ≤
        24 * totalDistance := by
    calc
      _ = |(dramSenseReluSquare (gate₁ - 1) -
              dramSenseReluSquare (gate₂ - 1)) -
            (dramSenseReluSquare (gate₁ - 1 - output₁) -
              dramSenseReluSquare (gate₂ - 1 - output₂))| := by
          congr 1
          ring
      _ ≤
          |dramSenseReluSquare (gate₁ - 1) -
              dramSenseReluSquare (gate₂ - 1)| +
            |dramSenseReluSquare (gate₁ - 1 - output₁) -
              dramSenseReluSquare (gate₂ - 1 - output₂)| :=
        abs_sub _ _
      _ ≤ 24 * totalDistance := by linarith
  rw [← mul_sub, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 20000)]
  nlinarith

theorem dramDifferentialSenseClampedNCurrent_dist_le_max
    (leftGate leftOutput rightGate rightOutput : ℝ) :
    dist
        (dramDifferentialSenseClampedNCurrent leftGate leftOutput)
        (dramDifferentialSenseClampedNCurrent rightGate rightOutput) ≤
      max (dist leftGate rightGate) (dist leftOutput rightOutput) := by
  simpa only [NNReal.coe_one, one_mul, Prod.dist_eq,
    Function.uncurry] using
    dramDifferentialSenseClampedNCurrent_lipschitz.dist_le_mul
      (leftGate, leftOutput) (rightGate, rightOutput)

abbrev DramDifferentialSensePair := ℝ × ℝ

noncomputable def dramDifferentialSensePairState
    (pair : DramDifferentialSensePair) :
    VectorState DramDifferentialSenseIndex
  | .trueLine => pair.1
  | .complementLine => pair.2

noncomputable def dramDifferentialSenseStatePair
    (state : VectorState DramDifferentialSenseIndex) :
    DramDifferentialSensePair :=
  (state .trueLine, state .complementLine)

@[simp]
theorem dramDifferentialSenseStatePair_pairState
    (pair : DramDifferentialSensePair) :
    dramDifferentialSenseStatePair
        (dramDifferentialSensePairState pair) = pair := by
  rfl

@[simp]
theorem dramDifferentialSensePairState_statePair
    (state : VectorState DramDifferentialSenseIndex) :
    dramDifferentialSensePairState
        (dramDifferentialSenseStatePair state) = state := by
  funext index
  cases index <;> rfl

/-- Globally Lipschitz proof extension of the exact nominal two-node latch
field. -/
noncomputable def dramDifferentialSenseNominalClampedPairRate
    (state : DramDifferentialSensePair) :
    DramDifferentialSensePair :=
  let trueVoltage := dramSenseVoltageClamp state.1
  let complementVoltage := dramSenseVoltageClamp state.2
  let trueNet :=
    dramDifferentialSenseClampedNCurrent
        (5 - complementVoltage) (5 - trueVoltage) -
      dramDifferentialSenseClampedNCurrent
        complementVoltage trueVoltage
  let complementNet :=
    dramDifferentialSenseClampedNCurrent
        (5 - trueVoltage) (5 - complementVoltage) -
      dramDifferentialSenseClampedNCurrent
        trueVoltage complementVoltage
  (trueNet / (3 / 10000000000000),
    complementNet / (3 / 10000000000000))

set_option maxHeartbeats 1200000 in
theorem dramDifferentialSenseNominalClampedPairRate_lipschitz :
    LipschitzWith (10000000000000 : NNReal)
      dramDifferentialSenseNominalClampedPairRate := by
  apply LipschitzWith.of_dist_le_mul
  intro left right
  let leftTrue := dramSenseVoltageClamp left.1
  let leftComplement := dramSenseVoltageClamp left.2
  let rightTrue := dramSenseVoltageClamp right.1
  let rightComplement := dramSenseVoltageClamp right.2
  let totalDistance := dist left right
  have htrueProjection :=
    dramSenseVoltageClamp_lipschitz.dist_le_mul left.1 right.1
  have hcomplementProjection :=
    dramSenseVoltageClamp_lipschitz.dist_le_mul left.2 right.2
  simp only [NNReal.coe_one, one_mul] at htrueProjection
  simp only [NNReal.coe_one, one_mul] at hcomplementProjection
  have htrueVoltage :
      dist leftTrue rightTrue ≤ totalDistance := by
    calc
      _ ≤ dist left.1 right.1 := by
        simpa only [leftTrue, rightTrue] using htrueProjection
      _ ≤ totalDistance := by
        dsimp only [totalDistance]
        rw [Prod.dist_eq]
        exact le_max_left _ _
  have hcomplementVoltage :
      dist leftComplement rightComplement ≤ totalDistance := by
    calc
      _ ≤ dist left.2 right.2 := by
        simpa only [leftComplement, rightComplement] using
          hcomplementProjection
      _ ≤ totalDistance := by
        dsimp only [totalDistance]
        rw [Prod.dist_eq]
        exact le_max_right _ _
  have htrueP :
      dist
          (dramDifferentialSenseClampedNCurrent
            (5 - leftComplement) (5 - leftTrue))
          (dramDifferentialSenseClampedNCurrent
            (5 - rightComplement) (5 - rightTrue)) ≤
        totalDistance := by
    have hgateDistance :
        dist (5 - leftComplement) (5 - rightComplement) =
          dist leftComplement rightComplement := by
      rw [Real.dist_eq, Real.dist_eq]
      calc
        |(5 - leftComplement) - (5 - rightComplement)| =
            |rightComplement - leftComplement| := by
          congr 1
          ring
        _ = |leftComplement - rightComplement| :=
          abs_sub_comm _ _
    have houtputDistance :
        dist (5 - leftTrue) (5 - rightTrue) =
          dist leftTrue rightTrue := by
      rw [Real.dist_eq, Real.dist_eq]
      calc
        |(5 - leftTrue) - (5 - rightTrue)| =
            |rightTrue - leftTrue| := by
          congr 1
          ring
        _ = |leftTrue - rightTrue| := abs_sub_comm _ _
    exact
      (dramDifferentialSenseClampedNCurrent_dist_le_max
        (5 - leftComplement) (5 - leftTrue)
        (5 - rightComplement) (5 - rightTrue)).trans
        (max_le
          (by rw [hgateDistance]; exact hcomplementVoltage)
          (by rw [houtputDistance]; exact htrueVoltage))
  have htrueN :
      dist
          (dramDifferentialSenseClampedNCurrent
            leftComplement leftTrue)
          (dramDifferentialSenseClampedNCurrent
            rightComplement rightTrue) ≤
        totalDistance :=
    (dramDifferentialSenseClampedNCurrent_dist_le_max
      leftComplement leftTrue rightComplement rightTrue).trans
      (max_le hcomplementVoltage htrueVoltage)
  have hcomplementP :
      dist
          (dramDifferentialSenseClampedNCurrent
            (5 - leftTrue) (5 - leftComplement))
          (dramDifferentialSenseClampedNCurrent
            (5 - rightTrue) (5 - rightComplement)) ≤
        totalDistance := by
    have hgateDistance :
        dist (5 - leftTrue) (5 - rightTrue) =
          dist leftTrue rightTrue := by
      rw [Real.dist_eq, Real.dist_eq]
      calc
        |(5 - leftTrue) - (5 - rightTrue)| =
            |rightTrue - leftTrue| := by
          congr 1
          ring
        _ = |leftTrue - rightTrue| := abs_sub_comm _ _
    have houtputDistance :
        dist (5 - leftComplement) (5 - rightComplement) =
          dist leftComplement rightComplement := by
      rw [Real.dist_eq, Real.dist_eq]
      calc
        |(5 - leftComplement) - (5 - rightComplement)| =
            |rightComplement - leftComplement| := by
          congr 1
          ring
        _ = |leftComplement - rightComplement| :=
          abs_sub_comm _ _
    exact
      (dramDifferentialSenseClampedNCurrent_dist_le_max
        (5 - leftTrue) (5 - leftComplement)
        (5 - rightTrue) (5 - rightComplement)).trans
        (max_le
          (by rw [hgateDistance]; exact htrueVoltage)
          (by rw [houtputDistance]; exact hcomplementVoltage))
  have hcomplementN :
      dist
          (dramDifferentialSenseClampedNCurrent
            leftTrue leftComplement)
          (dramDifferentialSenseClampedNCurrent
            rightTrue rightComplement) ≤
        totalDistance :=
    (dramDifferentialSenseClampedNCurrent_dist_le_max
      leftTrue leftComplement rightTrue rightComplement).trans
      (max_le htrueVoltage hcomplementVoltage)
  let leftTrueNet :=
    dramDifferentialSenseClampedNCurrent
        (5 - leftComplement) (5 - leftTrue) -
      dramDifferentialSenseClampedNCurrent leftComplement leftTrue
  let rightTrueNet :=
    dramDifferentialSenseClampedNCurrent
        (5 - rightComplement) (5 - rightTrue) -
      dramDifferentialSenseClampedNCurrent rightComplement rightTrue
  let leftComplementNet :=
    dramDifferentialSenseClampedNCurrent
        (5 - leftTrue) (5 - leftComplement) -
      dramDifferentialSenseClampedNCurrent leftTrue leftComplement
  let rightComplementNet :=
    dramDifferentialSenseClampedNCurrent
        (5 - rightTrue) (5 - rightComplement) -
      dramDifferentialSenseClampedNCurrent rightTrue rightComplement
  have htrueNet :
      dist leftTrueNet rightTrueNet ≤ 2 * totalDistance := by
    rw [Real.dist_eq]
    change
      |(dramDifferentialSenseClampedNCurrent
            (5 - leftComplement) (5 - leftTrue) -
          dramDifferentialSenseClampedNCurrent
            leftComplement leftTrue) -
        (dramDifferentialSenseClampedNCurrent
            (5 - rightComplement) (5 - rightTrue) -
          dramDifferentialSenseClampedNCurrent
            rightComplement rightTrue)| ≤
        2 * totalDistance
    calc
      _ ≤
          |dramDifferentialSenseClampedNCurrent
              (5 - leftComplement) (5 - leftTrue) -
            dramDifferentialSenseClampedNCurrent
              (5 - rightComplement) (5 - rightTrue)| +
          |dramDifferentialSenseClampedNCurrent
              leftComplement leftTrue -
            dramDifferentialSenseClampedNCurrent
              rightComplement rightTrue| := by
        rw [show
          (dramDifferentialSenseClampedNCurrent
                (5 - leftComplement) (5 - leftTrue) -
              dramDifferentialSenseClampedNCurrent
                leftComplement leftTrue) -
            (dramDifferentialSenseClampedNCurrent
                (5 - rightComplement) (5 - rightTrue) -
              dramDifferentialSenseClampedNCurrent
                rightComplement rightTrue) =
            (dramDifferentialSenseClampedNCurrent
                (5 - leftComplement) (5 - leftTrue) -
              dramDifferentialSenseClampedNCurrent
                (5 - rightComplement) (5 - rightTrue)) -
            (dramDifferentialSenseClampedNCurrent
                leftComplement leftTrue -
              dramDifferentialSenseClampedNCurrent
                rightComplement rightTrue) by ring]
        exact abs_sub _ _
      _ ≤ 2 * totalDistance := by
        rw [← Real.dist_eq, ← Real.dist_eq]
        linarith
  have hcomplementNet :
      dist leftComplementNet rightComplementNet ≤
        2 * totalDistance := by
    rw [Real.dist_eq]
    change
      |(dramDifferentialSenseClampedNCurrent
            (5 - leftTrue) (5 - leftComplement) -
          dramDifferentialSenseClampedNCurrent
            leftTrue leftComplement) -
        (dramDifferentialSenseClampedNCurrent
            (5 - rightTrue) (5 - rightComplement) -
          dramDifferentialSenseClampedNCurrent
            rightTrue rightComplement)| ≤
        2 * totalDistance
    calc
      _ ≤
          |dramDifferentialSenseClampedNCurrent
              (5 - leftTrue) (5 - leftComplement) -
            dramDifferentialSenseClampedNCurrent
              (5 - rightTrue) (5 - rightComplement)| +
          |dramDifferentialSenseClampedNCurrent
              leftTrue leftComplement -
            dramDifferentialSenseClampedNCurrent
              rightTrue rightComplement| := by
        rw [show
          (dramDifferentialSenseClampedNCurrent
                (5 - leftTrue) (5 - leftComplement) -
              dramDifferentialSenseClampedNCurrent
                leftTrue leftComplement) -
            (dramDifferentialSenseClampedNCurrent
                (5 - rightTrue) (5 - rightComplement) -
              dramDifferentialSenseClampedNCurrent
                rightTrue rightComplement) =
            (dramDifferentialSenseClampedNCurrent
                (5 - leftTrue) (5 - leftComplement) -
              dramDifferentialSenseClampedNCurrent
                (5 - rightTrue) (5 - rightComplement)) -
            (dramDifferentialSenseClampedNCurrent
                leftTrue leftComplement -
              dramDifferentialSenseClampedNCurrent
                rightTrue rightComplement) by ring]
        exact abs_sub _ _
      _ ≤ 2 * totalDistance := by
        rw [← Real.dist_eq, ← Real.dist_eq]
        linarith
  have hscaled
      {leftNet rightNet : ℝ}
      (hnet : dist leftNet rightNet ≤ 2 * totalDistance) :
      dist
          (leftNet / (3 / 10000000000000))
          (rightNet / (3 / 10000000000000)) ≤
        10000000000000 * totalDistance := by
    rw [Real.dist_eq, ← sub_div, abs_div]
    rw [Real.dist_eq] at hnet
    norm_num
    nlinarith [dist_nonneg (x := left) (y := right)]
  change
    dist
      (leftTrueNet / (3 / 10000000000000),
        leftComplementNet / (3 / 10000000000000))
      (rightTrueNet / (3 / 10000000000000),
        rightComplementNet / (3 / 10000000000000)) ≤
      (10000000000000 : ℝ) * totalDistance
  rw [Prod.dist_eq]
  exact max_le (hscaled htrueNet) (hscaled hcomplementNet)

/-- Exact agreement of the proof extension with the primitive source-derived
DAE on the rail-validity square. -/
theorem dramDifferentialSenseNominalClampedPairRate_residual
    {world : DramDifferentialSenseWorld}
    {state : DramDifferentialSensePair}
    {time : ℝ}
    (hsupply : world.environment.supply = 5)
    (hinstance :
      world.fabricated = nominalDramDifferentialSenseInstance)
    (hdomain :
      0 ≤ state.1 ∧ state.1 ≤ 5 ∧
        0 ≤ state.2 ∧ state.2 ≤ 5) :
    dramDifferentialSenseDAE.residual world time
      (dramDifferentialSensePairState state)
      (dramDifferentialSensePairState
        (dramDifferentialSenseNominalClampedPairRate state)) := by
  rcases hdomain with ⟨htrue0, htrue5, hcomplement0, hcomplement5⟩
  have htrueClamp :
      dramSenseVoltageClamp state.1 = state.1 :=
    dramSenseVoltageClamp_eq htrue0 htrue5
  have hcomplementClamp :
      dramSenseVoltageClamp state.2 = state.2 :=
    dramSenseVoltageClamp_eq hcomplement0 hcomplement5
  have htrueN :
      dramDifferentialSenseClampedNCurrent state.2 state.1 =
        dramDifferentialSenseNCurrent
          nominalDramDifferentialSenseInstance state.2 state.1 :=
    dramDifferentialSenseClampedNCurrent_eq_nominal
      hcomplement5 htrue0
  have hcomplementN :
      dramDifferentialSenseClampedNCurrent state.1 state.2 =
        dramDifferentialSenseNCurrent
          nominalDramDifferentialSenseInstance state.1 state.2 :=
    dramDifferentialSenseClampedNCurrent_eq_nominal
      htrue5 hcomplement0
  have htrueP :
      dramDifferentialSenseClampedNCurrent
          (5 - state.2) (5 - state.1) =
        dramDifferentialSensePCurrent
          nominalDramDifferentialSenseInstance
          5 state.2 state.1 := by
    rw [dramDifferentialSensePCurrent_eq_complementNCurrent
      5 state.2 state.1 rfl rfl]
    exact dramDifferentialSenseClampedNCurrent_eq_nominal
      (by linarith) (by linarith)
  have hcomplementP :
      dramDifferentialSenseClampedNCurrent
          (5 - state.1) (5 - state.2) =
        dramDifferentialSensePCurrent
          nominalDramDifferentialSenseInstance
          5 state.1 state.2 := by
    rw [dramDifferentialSensePCurrent_eq_complementNCurrent
      5 state.1 state.2 rfl rfl]
    exact dramDifferentialSenseClampedNCurrent_eq_nominal
      (by linarith) (by linarith)
  change
    world.fabricated.trueCapacitance *
          (dramDifferentialSenseNominalClampedPairRate state).1 +
        dramDifferentialSenseNCurrent world.fabricated state.2 state.1 -
        dramDifferentialSensePCurrent world.fabricated
          world.environment.supply state.2 state.1 = 0 ∧
      world.fabricated.complementCapacitance *
          (dramDifferentialSenseNominalClampedPairRate state).2 +
        dramDifferentialSenseNCurrent world.fabricated state.1 state.2 -
        dramDifferentialSensePCurrent world.fabricated
          world.environment.supply state.1 state.2 = 0
  rw [hinstance, hsupply]
  simp only [nominalDramDifferentialSenseInstance,
    dramDifferentialSenseNominalClampedPairRate,
    htrueClamp, hcomplementClamp]
  simp only [nominalDramDifferentialSenseInstance] at htrueN
  simp only [nominalDramDifferentialSenseInstance] at hcomplementN
  simp only [nominalDramDifferentialSenseInstance] at htrueP
  simp only [nominalDramDifferentialSenseInstance] at hcomplementP
  rw [← htrueN, ← hcomplementN, ← htrueP, ← hcomplementP]
  constructor <;> field_simp <;> ring

/-- Inside the nominal rail domain, the two positive capacitor equations
determine the derivative uniquely. Consequently every derivative satisfying
the primitive source DAE is exactly the clamped proof field. -/
theorem dramDifferentialSenseNominalClampedPairRate_eq_of_residual
    {world : DramDifferentialSenseWorld}
    {state derivative : VectorState DramDifferentialSenseIndex}
    {time : ℝ}
    (hsupply : world.environment.supply = 5)
    (hinstance :
      world.fabricated = nominalDramDifferentialSenseInstance)
    (hdomain : DramDifferentialSenseStateInRailDomain world state)
    (hresidual :
      dramDifferentialSenseDAE.residual world time state derivative) :
    derivative =
      dramDifferentialSensePairState
        (dramDifferentialSenseNominalClampedPairRate
          (dramDifferentialSenseStatePair state)) := by
  have hdomainFive :
      0 ≤ (dramDifferentialSenseStatePair state).1 ∧
        (dramDifferentialSenseStatePair state).1 ≤ 5 ∧
        0 ≤ (dramDifferentialSenseStatePair state).2 ∧
        (dramDifferentialSenseStatePair state).2 ≤ 5 := by
    unfold DramDifferentialSenseStateInRailDomain at hdomain
    rw [hsupply] at hdomain
    exact hdomain
  have hcanonical :=
    dramDifferentialSenseNominalClampedPairRate_residual
      (world := world) (time := time)
      hsupply hinstance hdomainFive
  rw [dramDifferentialSensePairState_statePair] at hcanonical
  dsimp only [dramDifferentialSenseDAE] at hresidual hcanonical
  rw [hinstance] at hresidual hcanonical
  funext index
  cases index
  · norm_num [nominalDramDifferentialSenseInstance] at hresidual hcanonical
    linarith [hresidual.1, hcanonical.1]
  · norm_num [nominalDramDifferentialSenseInstance] at hresidual hcanonical
    linarith [hresidual.2, hcanonical.2]

/-- Every coordinate of an absolutely-continuous nominal latch behavior is a
pointwise solution of the clamped proof ODE on the closed horizon. Absolute
continuity supplies the fundamental-theorem identity; the almost-everywhere
primitive residual and derivative uniqueness replace its integrand by the
continuous source field. -/
theorem
    dramDifferentialSenseNominalClampedPairRate_coordinate_hasDerivWithinAt
    {world : DramDifferentialSenseWorld}
    {trace : VectorTrace DramDifferentialSenseIndex}
    {horizon time : ℝ}
    (hsupply : world.environment.supply = 5)
    (hinstance :
      world.fabricated = nominalDramDifferentialSenseInstance)
    (hbehavior :
      dramDifferentialSenseDAE.ACBehavesOn world horizon trace)
    (hinvariant :
      ∀ point ∈ Set.Icc (0 : ℝ) horizon,
        DramDifferentialSenseStateInRailDomain world (trace point))
    (htime : time ∈ Set.Icc (0 : ℝ) horizon)
    (index : DramDifferentialSenseIndex) :
    HasDerivWithinAt (fun point => trace point index)
      ((dramDifferentialSensePairState
        (dramDifferentialSenseNominalClampedPairRate
          (dramDifferentialSenseStatePair (trace time)))) index)
      (Set.Icc (0 : ℝ) horizon) time := by
  let pairTrace : ℝ → DramDifferentialSensePair :=
    fun point => dramDifferentialSenseStatePair (trace point)
  let fieldTrace : ℝ → ℝ := fun point =>
    (dramDifferentialSensePairState
      (dramDifferentialSenseNominalClampedPairRate
        (pairTrace point))) index
  let primitive : ℝ → ℝ := fun point =>
    trace 0 index + ∫ target in (0 : ℝ)..point, fieldTrace target
  have htrueContinuous :
      ContinuousOn (fun point => trace point .trueLine)
        (Set.Icc (0 : ℝ) horizon) := by
    have hcontinuous := (hbehavior.2.1 .trueLine).continuousOn
    rwa [Set.uIcc_of_le hbehavior.1] at hcontinuous
  have hcomplementContinuous :
      ContinuousOn (fun point => trace point .complementLine)
        (Set.Icc (0 : ℝ) horizon) := by
    have hcontinuous := (hbehavior.2.1 .complementLine).continuousOn
    rwa [Set.uIcc_of_le hbehavior.1] at hcontinuous
  have hpairTraceContinuous :
      ContinuousOn pairTrace (Set.Icc (0 : ℝ) horizon) := by
    simpa only [pairTrace, dramDifferentialSenseStatePair] using
      htrueContinuous.prodMk hcomplementContinuous
  have hfieldPairContinuous :
      ContinuousOn
        (fun point =>
          dramDifferentialSenseNominalClampedPairRate
            (pairTrace point))
        (Set.Icc (0 : ℝ) horizon) :=
    dramDifferentialSenseNominalClampedPairRate_lipschitz.continuous
      |>.continuousOn.comp hpairTraceContinuous
        (fun _point _hpoint => Set.mem_univ _)
  have hfieldTraceContinuous :
      ContinuousOn fieldTrace (Set.Icc (0 : ℝ) horizon) := by
    cases index
    · have hcontinuous :=
        continuous_fst.comp_continuousOn hfieldPairContinuous
      change
        ContinuousOn
          (fun point =>
            (dramDifferentialSenseNominalClampedPairRate
              (pairTrace point)).1)
          (Set.Icc (0 : ℝ) horizon) at hcontinuous
      exact hcontinuous
    · have hcontinuous :=
        continuous_snd.comp_continuousOn hfieldPairContinuous
      change
        ContinuousOn
          (fun point =>
            (dramDifferentialSenseNominalClampedPairRate
              (pairTrace point)).2)
          (Set.Icc (0 : ℝ) horizon) at hcontinuous
      exact hcontinuous
  have hderivativeEq :
      ∀ᵐ point ∂MeasureTheory.volume.restrict
          (Set.uIcc (0 : ℝ) horizon),
        deriv (fun target => trace target index) point =
          fieldTrace point := by
    filter_upwards [hbehavior.2.2,
      MeasureTheory.ae_restrict_mem measurableSet_uIcc]
      with point hpoint hpointDomain
    obtain ⟨derivative, htraceDerivative, hresidual⟩ := hpoint
    rw [Set.uIcc_of_le hbehavior.1] at hpointDomain
    have hfield :=
      dramDifferentialSenseNominalClampedPairRate_eq_of_residual
        hsupply hinstance (hinvariant point hpointDomain) hresidual
    rw [(htraceDerivative index).deriv]
    exact congrFun hfield index
  have hderivativeEq' :
      ∀ᵐ point, point ∈ Set.uIcc (0 : ℝ) horizon →
        deriv (fun target => trace target index) point =
          fieldTrace point :=
    MeasureTheory.ae_imp_of_ae_restrict hderivativeEq
  have htraceEqPrimitive :
      Set.EqOn (fun point => trace point index) primitive
        (Set.Icc (0 : ℝ) horizon) := by
    intro point hpoint
    have hsubinterval :
        Set.uIcc (0 : ℝ) point ⊆ Set.uIcc (0 : ℝ) horizon := by
      rw [Set.uIcc_of_le hpoint.1, Set.uIcc_of_le hbehavior.1]
      intro target htarget
      exact ⟨htarget.1, htarget.2.trans hpoint.2⟩
    have htraceACSub :
        AbsolutelyContinuousOnInterval
          (fun target => trace target index) 0 point :=
      (hbehavior.2.1 index).mono hsubinterval
    have hintegrals :
        (∫ target in (0 : ℝ)..point,
            deriv (fun target => trace target index) target) =
          ∫ target in (0 : ℝ)..point, fieldTrace target := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hderivativeEq'] with target htarget
      intro htargetInterval
      apply htarget
      exact hsubinterval (Set.uIoc_subset_uIcc htargetInterval)
    have hfundamental := htraceACSub.integral_deriv_eq_sub
    dsimp only [primitive]
    rw [← hintegrals, hfundamental]
    ring
  have hfieldTraceIntegrable :
      IntervalIntegrable fieldTrace MeasureTheory.volume 0 time :=
    (hfieldTraceContinuous.mono
      (Set.uIcc_subset_Icc
        ⟨le_rfl, hbehavior.1⟩ htime)).intervalIntegrable
  letI : Fact (time ∈ Set.Icc (0 : ℝ) horizon) := ⟨htime⟩
  have hintegralDerivative :
      HasDerivWithinAt
        (fun point => ∫ target in (0 : ℝ)..point, fieldTrace target)
        (fieldTrace time) (Set.Icc (0 : ℝ) horizon) time :=
    intervalIntegral.integral_hasDerivWithinAt_right
      hfieldTraceIntegrable
      (hfieldTraceContinuous
        |>.stronglyMeasurableAtFilter_nhdsWithin
          measurableSet_Icc time)
      (hfieldTraceContinuous time htime)
  have hprimitiveDerivative :
      HasDerivWithinAt primitive (fieldTrace time)
        (Set.Icc (0 : ℝ) horizon) time := by
    simpa only [primitive, zero_add] using
      hintegralDerivative.const_add (trace 0 index)
  exact hprimitiveDerivative.congr
    (fun point hpoint => htraceEqPrimitive hpoint)
    (htraceEqPrimitive htime)

/-- Pair-valued form of the absolutely-continuous-to-pointwise upgrade. -/
theorem dramDifferentialSenseNominalClampedPairRate_hasDerivWithinAt
    {world : DramDifferentialSenseWorld}
    {trace : VectorTrace DramDifferentialSenseIndex}
    {horizon time : ℝ}
    (hsupply : world.environment.supply = 5)
    (hinstance :
      world.fabricated = nominalDramDifferentialSenseInstance)
    (hbehavior :
      dramDifferentialSenseDAE.ACBehavesOn world horizon trace)
    (hinvariant :
      ∀ point ∈ Set.Icc (0 : ℝ) horizon,
        DramDifferentialSenseStateInRailDomain world (trace point))
    (htime : time ∈ Set.Icc (0 : ℝ) horizon) :
    HasDerivWithinAt
      (fun point => dramDifferentialSenseStatePair (trace point))
      (dramDifferentialSenseNominalClampedPairRate
        (dramDifferentialSenseStatePair (trace time)))
      (Set.Icc (0 : ℝ) horizon) time := by
  have htrue :=
    dramDifferentialSenseNominalClampedPairRate_coordinate_hasDerivWithinAt
      hsupply hinstance hbehavior hinvariant htime
        DramDifferentialSenseIndex.trueLine
  have hcomplement :=
    dramDifferentialSenseNominalClampedPairRate_coordinate_hasDerivWithinAt
      hsupply hinstance hbehavior hinvariant htime
        DramDifferentialSenseIndex.complementLine
  simpa only [dramDifferentialSenseStatePair,
    dramDifferentialSensePairState] using
      htrue.prodMk hcomplement

theorem dramSenseReluSquare_le_sixteen (value : ℝ) :
    dramSenseReluSquare value ≤ 16 := by
  unfold dramSenseReluSquare
  let projected : ℝ :=
    Set.projIcc (0 : ℝ) 4 (by norm_num) value
  have hbounds :
      0 ≤ projected ∧ projected ≤ 4 :=
    (Set.projIcc (0 : ℝ) 4 (by norm_num) value).property
  change projected ^ 2 ≤ 16
  nlinarith [mul_nonneg hbounds.1 (sub_nonneg.mpr hbounds.2)]

@[simp]
theorem dramDifferentialSenseClampedNCurrent_zero_output
    (gate : ℝ) :
    dramDifferentialSenseClampedNCurrent gate 0 = 0 := by
  simp [dramDifferentialSenseClampedNCurrent]

theorem dramDifferentialSenseClampedNCurrent_nonnegative
    {gate output : ℝ}
    (hgateUpper : gate ≤ 5)
    (houtput0 : 0 ≤ output) :
    0 ≤ dramDifferentialSenseClampedNCurrent gate output := by
  rw [dramDifferentialSenseClampedNCurrent_eq_nominal
    hgateUpper houtput0]
  exact mos1ForwardCurrent_nonneg .nmos 1 (1 / 10000)
    gate output (by norm_num) houtput0

theorem dramDifferentialSenseClampedNCurrent_abs_le_one
    (gate output : ℝ) :
    |dramDifferentialSenseClampedNCurrent gate output| ≤ 1 := by
  unfold dramDifferentialSenseClampedNCurrent
  rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 20000)]
  have hdifference :=
    abs_sub
      (dramSenseReluSquare (gate - 1))
      (dramSenseReluSquare (gate - 1 - output))
  have hfirst0 := dramSenseReluSquare_nonnegative (gate - 1)
  have hsecond0 :=
    dramSenseReluSquare_nonnegative (gate - 1 - output)
  have hfirst16 := dramSenseReluSquare_le_sixteen (gate - 1)
  have hsecond16 :=
    dramSenseReluSquare_le_sixteen (gate - 1 - output)
  rw [abs_of_nonneg hfirst0, abs_of_nonneg hsecond0] at hdifference
  nlinarith

theorem dramDifferentialSenseNominalClampedPairRate_norm_le
    (state : DramDifferentialSensePair) :
    ‖dramDifferentialSenseNominalClampedPairRate state‖ ≤
      10000000000000 := by
  let trueVoltage := dramSenseVoltageClamp state.1
  let complementVoltage := dramSenseVoltageClamp state.2
  have htrueP :=
    dramDifferentialSenseClampedNCurrent_abs_le_one
      (5 - complementVoltage) (5 - trueVoltage)
  have htrueN :=
    dramDifferentialSenseClampedNCurrent_abs_le_one
      complementVoltage trueVoltage
  have hcomplementP :=
    dramDifferentialSenseClampedNCurrent_abs_le_one
      (5 - trueVoltage) (5 - complementVoltage)
  have hcomplementN :=
    dramDifferentialSenseClampedNCurrent_abs_le_one
      trueVoltage complementVoltage
  have htrueNet :
      |dramDifferentialSenseClampedNCurrent
            (5 - complementVoltage) (5 - trueVoltage) -
          dramDifferentialSenseClampedNCurrent
            complementVoltage trueVoltage| ≤ 2 := by
    exact (abs_sub _ _).trans (by linarith)
  have hcomplementNet :
      |dramDifferentialSenseClampedNCurrent
            (5 - trueVoltage) (5 - complementVoltage) -
          dramDifferentialSenseClampedNCurrent
            trueVoltage complementVoltage| ≤ 2 := by
    exact (abs_sub _ _).trans (by linarith)
  rw [Prod.norm_def]
  apply max_le
  · change
      |(dramDifferentialSenseClampedNCurrent
            (5 - complementVoltage) (5 - trueVoltage) -
          dramDifferentialSenseClampedNCurrent
            complementVoltage trueVoltage) /
        (3 / 10000000000000)| ≤ 10000000000000
    rw [abs_div]
    norm_num
    nlinarith
  · change
      |(dramDifferentialSenseClampedNCurrent
            (5 - trueVoltage) (5 - complementVoltage) -
          dramDifferentialSenseClampedNCurrent
            trueVoltage complementVoltage) /
        (3 / 10000000000000)| ≤ 10000000000000
    rw [abs_div]
    norm_num
    nlinarith

/-- A solution of the globally clamped proof field exists for every finite
nonnegative horizon and every initial pair. -/
theorem dramDifferentialSenseNominalClampedPairRate_realizable
    (initial : DramDifferentialSensePair)
    {horizon : ℝ} (hhorizon : 0 ≤ horizon) :
    ∃ trajectory : ℝ → DramDifferentialSensePair,
      trajectory 0 = initial ∧
      ∀ time ∈ Set.Icc (0 : ℝ) horizon,
        HasDerivWithinAt trajectory
          (dramDifferentialSenseNominalClampedPairRate (trajectory time))
          (Set.Icc (0 : ℝ) horizon) time := by
  let horizonNN : NNReal := ⟨horizon, hhorizon⟩
  let bound : NNReal := 10000000000000
  let radius : NNReal := bound * horizonNN
  let initialTime : Set.Icc (0 : ℝ) horizon :=
    ⟨0, le_rfl, hhorizon⟩
  have hpl :
      IsPicardLindelof
        (fun _time : ℝ =>
          dramDifferentialSenseNominalClampedPairRate)
        initialTime initial radius 0
        bound 10000000000000 := by
    apply IsPicardLindelof.of_time_independent
    · intro state _hstate
      exact dramDifferentialSenseNominalClampedPairRate_norm_le state
    · exact
        dramDifferentialSenseNominalClampedPairRate_lipschitz
          |>.lipschitzOnWith
    · dsimp [radius, bound, horizonNN, initialTime]
      simp only [sub_zero, max_eq_left hhorizon]
      exact le_rfl
  simpa [initialTime] using
    hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

/-- At the lower true-line rail the clamped field points inward. -/
theorem dramDifferentialSenseNominalClampedPairRate_true_nonnegative
    (complement : ℝ) :
    0 ≤
      (dramDifferentialSenseNominalClampedPairRate
        (0, complement)).1 := by
  let complementVoltage := dramSenseVoltageClamp complement
  have hcomplementBounds :
      0 ≤ complementVoltage ∧ complementVoltage ≤ 5 :=
    (Set.projIcc (0 : ℝ) 5 (by norm_num) complement).property
  have hp :
      0 ≤ dramDifferentialSenseClampedNCurrent
        (5 - complementVoltage) 5 := by
    exact dramDifferentialSenseClampedNCurrent_nonnegative
      (by linarith) (by norm_num)
  have hzero : dramSenseVoltageClamp 0 = 0 :=
    dramSenseVoltageClamp_eq (by norm_num) (by norm_num)
  change
    0 ≤
      (dramDifferentialSenseClampedNCurrent
            (5 - dramSenseVoltageClamp complement)
            (5 - dramSenseVoltageClamp 0) -
          dramDifferentialSenseClampedNCurrent
            (dramSenseVoltageClamp complement)
            (dramSenseVoltageClamp 0)) /
        (3 / 10000000000000)
  rw [hzero]
  simp only [sub_zero,
    dramDifferentialSenseClampedNCurrent_zero_output]
  exact div_nonneg (by simpa [complementVoltage] using hp) (by norm_num)

/-- At the upper true-line rail the clamped field points inward. -/
theorem dramDifferentialSenseNominalClampedPairRate_true_nonpositive
    (complement : ℝ) :
    (dramDifferentialSenseNominalClampedPairRate
      (5, complement)).1 ≤ 0 := by
  let complementVoltage := dramSenseVoltageClamp complement
  have hcomplementBounds :
      0 ≤ complementVoltage ∧ complementVoltage ≤ 5 :=
    (Set.projIcc (0 : ℝ) 5 (by norm_num) complement).property
  have hn :
      0 ≤ dramDifferentialSenseClampedNCurrent
        complementVoltage 5 := by
    exact dramDifferentialSenseClampedNCurrent_nonnegative
      hcomplementBounds.2 (by norm_num)
  have hfive : dramSenseVoltageClamp 5 = 5 :=
    dramSenseVoltageClamp_eq (by norm_num) (by norm_num)
  change
    (dramDifferentialSenseClampedNCurrent
          (5 - dramSenseVoltageClamp complement)
          (5 - dramSenseVoltageClamp 5) -
        dramDifferentialSenseClampedNCurrent
          (dramSenseVoltageClamp complement)
          (dramSenseVoltageClamp 5)) /
      (3 / 10000000000000) ≤ 0
  rw [hfive]
  simp only [sub_self,
    dramDifferentialSenseClampedNCurrent_zero_output, zero_sub]
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (by simpa [complementVoltage] using hn))
    (by norm_num)

theorem dramDifferentialSenseNominalClampedPairRate_complement_nonnegative
    (trueVoltage : ℝ) :
    0 ≤
      (dramDifferentialSenseNominalClampedPairRate
        (trueVoltage, 0)).2 := by
  have :=
    dramDifferentialSenseNominalClampedPairRate_true_nonnegative
      trueVoltage
  simpa only [dramDifferentialSenseNominalClampedPairRate] using this

theorem dramDifferentialSenseNominalClampedPairRate_complement_nonpositive
    (trueVoltage : ℝ) :
    (dramDifferentialSenseNominalClampedPairRate
      (trueVoltage, 5)).2 ≤ 0 := by
  have :=
    dramDifferentialSenseNominalClampedPairRate_true_nonpositive
      trueVoltage
  simpa only [dramDifferentialSenseNominalClampedPairRate] using this

theorem dramSenseVoltageClamp_eq_zero_of_le
    {value : ℝ} (hvalue : value ≤ 0) :
    dramSenseVoltageClamp value = 0 := by
  exact congrArg Subtype.val
    (Set.projIcc_of_le_left (by norm_num) hvalue)

theorem dramSenseVoltageClamp_eq_five_of_le
    {value : ℝ} (hvalue : 5 ≤ value) :
    dramSenseVoltageClamp value = 5 := by
  exact congrArg Subtype.val
    (Set.projIcc_of_right_le (by norm_num) hvalue)

theorem dramDifferentialSenseNominalClampedPairRate_true_nonnegative_of_le
    {trueVoltage complementVoltage : ℝ}
    (htrue : trueVoltage ≤ 0) :
    0 ≤
      (dramDifferentialSenseNominalClampedPairRate
        (trueVoltage, complementVoltage)).1 := by
  have hclamp :=
    dramSenseVoltageClamp_eq_zero_of_le htrue
  have hzero : dramSenseVoltageClamp 0 = 0 :=
    dramSenseVoltageClamp_eq (by norm_num) (by norm_num)
  simpa only [dramDifferentialSenseNominalClampedPairRate, hclamp,
    hzero] using
    dramDifferentialSenseNominalClampedPairRate_true_nonnegative
      complementVoltage

theorem dramDifferentialSenseNominalClampedPairRate_true_nonpositive_of_le
    {trueVoltage complementVoltage : ℝ}
    (htrue : 5 ≤ trueVoltage) :
    (dramDifferentialSenseNominalClampedPairRate
      (trueVoltage, complementVoltage)).1 ≤ 0 := by
  have hclamp :=
    dramSenseVoltageClamp_eq_five_of_le htrue
  have hfive : dramSenseVoltageClamp 5 = 5 :=
    dramSenseVoltageClamp_eq (by norm_num) (by norm_num)
  simpa only [dramDifferentialSenseNominalClampedPairRate, hclamp,
    hfive] using
    dramDifferentialSenseNominalClampedPairRate_true_nonpositive
      complementVoltage

theorem
    dramDifferentialSenseNominalClampedPairRate_complement_nonnegative_of_le
    {trueVoltage complementVoltage : ℝ}
    (hcomplement : complementVoltage ≤ 0) :
    0 ≤
      (dramDifferentialSenseNominalClampedPairRate
        (trueVoltage, complementVoltage)).2 := by
  have hclamp :=
    dramSenseVoltageClamp_eq_zero_of_le hcomplement
  have hzero : dramSenseVoltageClamp 0 = 0 :=
    dramSenseVoltageClamp_eq (by norm_num) (by norm_num)
  simpa only [dramDifferentialSenseNominalClampedPairRate, hclamp,
    hzero] using
    dramDifferentialSenseNominalClampedPairRate_complement_nonnegative
      trueVoltage

theorem
    dramDifferentialSenseNominalClampedPairRate_complement_nonpositive_of_le
    {trueVoltage complementVoltage : ℝ}
    (hcomplement : 5 ≤ complementVoltage) :
    (dramDifferentialSenseNominalClampedPairRate
      (trueVoltage, complementVoltage)).2 ≤ 0 := by
  have hclamp :=
    dramSenseVoltageClamp_eq_five_of_le hcomplement
  have hfive : dramSenseVoltageClamp 5 = 5 :=
    dramSenseVoltageClamp_eq (by norm_num) (by norm_num)
  simpa only [dramDifferentialSenseNominalClampedPairRate, hclamp,
    hfive] using
    dramDifferentialSenseNominalClampedPairRate_complement_nonpositive
      trueVoltage

private theorem scalar_solution_upper_invariant
    {trajectory derivative : ℝ → ℝ}
    {horizon rail : ℝ}
    (hhorizon : 0 ≤ horizon)
    (hinitial : trajectory 0 ≤ rail)
    (hsolution :
      ∀ time ∈ Set.Icc (0 : ℝ) horizon,
        HasDerivWithinAt trajectory (derivative time)
          (Set.Icc (0 : ℝ) horizon) time)
    (hinward :
      ∀ time ∈ Set.Ico (0 : ℝ) horizon,
        rail ≤ trajectory time → derivative time ≤ 0) :
    ∀ time ∈ Set.Icc (0 : ℝ) horizon,
      trajectory time ≤ rail := by
  have hcontinuous :
      ContinuousOn trajectory (Set.Icc (0 : ℝ) horizon) := by
    intro time htime
    exact (hsolution time htime).continuousWithinAt
  intro time htime
  apply le_of_forall_pos_le_add
  intro epsilon hepsilon
  let slope : ℝ := epsilon / (horizon + 1)
  have hslope : 0 < slope := by
    dsimp [slope]
    exact div_pos hepsilon (by linarith)
  have hrightDerivative :
      ∀ point ∈ Set.Ico (0 : ℝ) horizon,
        HasDerivWithinAt trajectory (derivative point)
          (Set.Ici point) point := by
    intro point hpoint
    exact
      ((hsolution point ⟨hpoint.1, hpoint.2.le⟩)
        |>.mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGT_of_mem hpoint)).Ici_of_Ioi
  have hbarrier :
      ∀ ⦃point⦄, point ∈ Set.Icc (0 : ℝ) horizon →
        trajectory point ≤ rail + slope * point := by
    refine image_le_of_deriv_right_lt_deriv_boundary
      (f := trajectory)
      (f' := derivative)
      (B := fun point => rail + slope * point)
      (B' := fun _point => slope)
      hcontinuous hrightDerivative ?_ ?_ ?_
    · simpa using hinitial
    · intro point
      exact
        (((hasDerivAt_id point).const_mul slope).const_add rail)
          |>.congr_deriv (by ring)
    · intro point hpoint heq
      have hrail : rail ≤ trajectory point := by
        rw [heq]
        exact le_add_of_nonneg_right
          (mul_nonneg hslope.le hpoint.1)
      have hrate := hinward point hpoint hrail
      linarith
  have htimeRatio : time / (horizon + 1) ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith [htime.2]
  have hslopeTime : slope * time ≤ epsilon := by
    calc
      slope * time = epsilon * (time / (horizon + 1)) := by
        dsimp [slope]
        field_simp
      _ ≤ epsilon * 1 :=
        mul_le_mul_of_nonneg_left htimeRatio hepsilon.le
      _ = epsilon := mul_one _
  exact (hbarrier htime).trans (by linarith)

private theorem scalar_solution_rail_invariant
    {trajectory derivative : ℝ → ℝ}
    {horizon : ℝ}
    (hhorizon : 0 ≤ horizon)
    (hinitial0 : 0 ≤ trajectory 0)
    (hinitial5 : trajectory 0 ≤ 5)
    (hsolution :
      ∀ time ∈ Set.Icc (0 : ℝ) horizon,
        HasDerivWithinAt trajectory (derivative time)
          (Set.Icc (0 : ℝ) horizon) time)
    (hlower :
      ∀ time ∈ Set.Ico (0 : ℝ) horizon,
        trajectory time ≤ 0 → 0 ≤ derivative time)
    (hupper :
      ∀ time ∈ Set.Ico (0 : ℝ) horizon,
        5 ≤ trajectory time → derivative time ≤ 0) :
    ∀ time ∈ Set.Icc (0 : ℝ) horizon,
      0 ≤ trajectory time ∧ trajectory time ≤ 5 := by
  have hu :=
    scalar_solution_upper_invariant hhorizon hinitial5 hsolution hupper
  have hnegativeSolution :
      ∀ time ∈ Set.Icc (0 : ℝ) horizon,
        HasDerivWithinAt (fun time => -trajectory time)
          (-derivative time) (Set.Icc (0 : ℝ) horizon) time := by
    intro time htime
    exact (hsolution time htime).neg
  have hl :=
    scalar_solution_upper_invariant
      (trajectory := fun time => -trajectory time)
      (derivative := fun time => -derivative time)
      (rail := 0)
      hhorizon (by linarith) hnegativeSolution
      (by
        intro time htime hboundary
        have hrate := hlower time htime (by linarith)
        linarith)
  intro time htime
  constructor
  · have := hl time htime
    linarith
  · exact hu time htime

private theorem hasDerivWithinAt_fst_of_pair
    {trajectory : ℝ → DramDifferentialSensePair}
    {rate : DramDifferentialSensePair}
    {domain : Set ℝ} {time : ℝ}
    (hderivative :
      HasDerivWithinAt trajectory rate domain time) :
    HasDerivWithinAt (fun time => (trajectory time).1)
      rate.1 domain time := by
  simpa using
    hderivative.hasFDerivWithinAt.fst.hasDerivWithinAt

private theorem hasDerivWithinAt_snd_of_pair
    {trajectory : ℝ → DramDifferentialSensePair}
    {rate : DramDifferentialSensePair}
    {domain : Set ℝ} {time : ℝ}
    (hderivative :
      HasDerivWithinAt trajectory rate domain time) :
    HasDerivWithinAt (fun time => (trajectory time).2)
      rate.2 domain time := by
  simpa using
    hderivative.hasFDerivWithinAt.snd.hasDerivWithinAt

/-- Every solution of the globally clamped nominal latch field that starts
inside the rail square remains inside it. This is the domain-closure step
that permits the clamped proof extension to be replaced by the primitive
MOS1/KCL residual everywhere along the physical trajectory. -/
theorem dramDifferentialSenseNominalClampedPairRate_invariant
    {trajectory : ℝ → DramDifferentialSensePair}
    {initial : DramDifferentialSensePair}
    {horizon : ℝ}
    (hhorizon : 0 ≤ horizon)
    (hinitial : trajectory 0 = initial)
    (hinitialTrue :
      initial.1 ∈ Set.Icc (0 : ℝ) 5)
    (hinitialComplement :
      initial.2 ∈ Set.Icc (0 : ℝ) 5)
    (hsolution :
      ∀ time ∈ Set.Icc (0 : ℝ) horizon,
        HasDerivWithinAt trajectory
          (dramDifferentialSenseNominalClampedPairRate
            (trajectory time))
          (Set.Icc (0 : ℝ) horizon) time) :
    ∀ time ∈ Set.Icc (0 : ℝ) horizon,
      (trajectory time).1 ∈ Set.Icc (0 : ℝ) 5 ∧
        (trajectory time).2 ∈ Set.Icc (0 : ℝ) 5 := by
  have htrueSolution :
      ∀ time ∈ Set.Icc (0 : ℝ) horizon,
        HasDerivWithinAt
          (fun time => (trajectory time).1)
          (dramDifferentialSenseNominalClampedPairRate
            (trajectory time)).1
          (Set.Icc (0 : ℝ) horizon) time := by
    intro time htime
    exact hasDerivWithinAt_fst_of_pair (hsolution time htime)
  have hcomplementSolution :
      ∀ time ∈ Set.Icc (0 : ℝ) horizon,
        HasDerivWithinAt
          (fun time => (trajectory time).2)
          (dramDifferentialSenseNominalClampedPairRate
            (trajectory time)).2
          (Set.Icc (0 : ℝ) horizon) time := by
    intro time htime
    exact hasDerivWithinAt_snd_of_pair (hsolution time htime)
  have htrue :=
    scalar_solution_rail_invariant
      hhorizon
      (by rw [hinitial]; exact hinitialTrue.1)
      (by rw [hinitial]; exact hinitialTrue.2)
      htrueSolution
      (by
        intro time _htime hlower
        exact
          dramDifferentialSenseNominalClampedPairRate_true_nonnegative_of_le
            hlower)
      (by
        intro time _htime hupper
        exact
          dramDifferentialSenseNominalClampedPairRate_true_nonpositive_of_le
            hupper)
  have hcomplement :=
    scalar_solution_rail_invariant
      hhorizon
      (by rw [hinitial]; exact hinitialComplement.1)
      (by rw [hinitial]; exact hinitialComplement.2)
      hcomplementSolution
      (by
        intro time _htime hlower
        exact
          dramDifferentialSenseNominalClampedPairRate_complement_nonnegative_of_le
            hlower)
      (by
        intro time _htime hupper
        exact
          dramDifferentialSenseNominalClampedPairRate_complement_nonpositive_of_le
            hupper)
  intro time htime
  exact ⟨htrue time htime, hcomplement time htime⟩

/-- The full unbalanced nominal latch is realizable for every finite
nonnegative horizon and every pair of initial voltages in the rail square.
The witness is an absolutely-continuous behavior of the source-derived
two-capacitor/four-MOS DAE, not an endpoint relation. Its domain invariant is
returned alongside the behavior. -/
theorem dramDifferentialSense_nominal_unbalanced_realizable
    {world : DramDifferentialSenseWorld}
    (hsupply : world.environment.supply = 5)
    (hinstance :
      world.fabricated = nominalDramDifferentialSenseInstance)
    (hhorizon : 0 ≤ world.environment.horizon)
    (hinitialTrue :
      world.environment.initialTrue ∈ Set.Icc (0 : ℝ) 5)
    (hinitialComplement :
      world.environment.initialComplement ∈ Set.Icc (0 : ℝ) 5) :
    ∃ boundary : DramDifferentialSenseBoundary,
      DramDifferentialSenseBehavior world boundary () ∧
      ∀ time ∈ Set.Icc (0 : ℝ) world.environment.horizon,
        boundary.voltage time .trueLine ∈ Set.Icc (0 : ℝ) 5 ∧
          boundary.voltage time .complementLine ∈
            Set.Icc (0 : ℝ) 5 := by
  let initial : DramDifferentialSensePair :=
    (world.environment.initialTrue,
      world.environment.initialComplement)
  obtain ⟨pairTrajectory, hpairInitial, hpairSolution⟩ :=
    dramDifferentialSenseNominalClampedPairRate_realizable
      initial hhorizon
  have hpairInvariant :
      ∀ time ∈ Set.Icc (0 : ℝ) world.environment.horizon,
        (pairTrajectory time).1 ∈ Set.Icc (0 : ℝ) 5 ∧
          (pairTrajectory time).2 ∈ Set.Icc (0 : ℝ) 5 :=
    dramDifferentialSenseNominalClampedPairRate_invariant
      hhorizon hpairInitial hinitialTrue hinitialComplement
        hpairSolution
  have hpairLipschitz :
      LipschitzOnWith (10000000000000 : NNReal)
        pairTrajectory
        (Set.Icc (0 : ℝ) world.environment.horizon) := by
    apply
      (convex_Icc (0 : ℝ) world.environment.horizon)
        |>.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
          hpairSolution
    intro time _htime
    rw [← NNReal.coe_le_coe]
    simpa only [coe_nnnorm, NNReal.coe_ofNat] using
      dramDifferentialSenseNominalClampedPairRate_norm_le
        (pairTrajectory time)
  let trace : VectorTrace DramDifferentialSenseIndex :=
    fun time =>
      dramDifferentialSensePairState (pairTrajectory time)
  have hcoordinateLipschitz :
      ∀ index,
        LipschitzOnWith (10000000000000 : NNReal)
          (fun time => trace time index)
          (Set.Icc (0 : ℝ) world.environment.horizon) := by
    intro index
    apply LipschitzOnWith.of_dist_le_mul
    intro left hleft right hright
    have hpair :=
      hpairLipschitz.dist_le_mul left hleft right hright
    cases index
    · exact
        (show
          dist (pairTrajectory left).1 (pairTrajectory right).1 ≤
            dist (pairTrajectory left) (pairTrajectory right) from by
              rw [Prod.dist_eq]
              exact le_max_left _ _).trans hpair
    · exact
        (show
          dist (pairTrajectory left).2 (pairTrajectory right).2 ≤
            dist (pairTrajectory left) (pairTrajectory right) from by
              rw [Prod.dist_eq]
              exact le_max_right _ _).trans hpair
  have habsolutelyContinuous :
      ∀ index,
        AbsolutelyContinuousOnInterval
          (fun time => trace time index)
          0 world.environment.horizon := by
    intro index
    have hlipschitz := hcoordinateLipschitz index
    rw [← Set.uIcc_of_le hhorizon] at hlipschitz
    exact hlipschitz.absolutelyContinuousOnInterval
  have hphysical :
      dramDifferentialSenseDAE.ACBehavesOn world
        world.environment.horizon trace := by
    refine ⟨hhorizon, habsolutelyContinuous, ?_⟩
    rw [Set.uIcc_of_le hhorizon,
      ← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
    intro time htime
    have htimeClosed :
        time ∈ Set.Icc (0 : ℝ) world.environment.horizon :=
      ⟨htime.1.le, htime.2.le⟩
    let rate :=
      dramDifferentialSenseNominalClampedPairRate
        (pairTrajectory time)
    let derivative : VectorState DramDifferentialSenseIndex :=
      dramDifferentialSensePairState rate
    refine ⟨derivative, ?_, ?_⟩
    · intro index
      cases index
      · exact
          (hasDerivWithinAt_fst_of_pair
            (hpairSolution time htimeClosed)).hasDerivAt
              (Icc_mem_nhds htime.1 htime.2)
      · exact
          (hasDerivWithinAt_snd_of_pair
            (hpairSolution time htimeClosed)).hasDerivAt
              (Icc_mem_nhds htime.1 htime.2)
    · have hdomain := hpairInvariant time htimeClosed
      exact
        dramDifferentialSenseNominalClampedPairRate_residual
          hsupply hinstance
          ⟨hdomain.1.1, hdomain.1.2,
            hdomain.2.1, hdomain.2.2⟩
  let boundary : DramDifferentialSenseBoundary :=
    { voltage := trace }
  refine ⟨boundary, ?_, ?_⟩
  · intro clause
    cases clause
    · change (pairTrajectory 0).1 =
        world.environment.initialTrue
      rw [hpairInitial]
    · change (pairTrajectory 0).2 =
        world.environment.initialComplement
      rw [hpairInitial]
    · exact hphysical
  · intro time htime
    exact hpairInvariant time htime

@[simp]
theorem dramDifferentialSenseNominalClampedPairRate_swap
    (state : DramDifferentialSensePair) :
    dramDifferentialSenseNominalClampedPairRate
        (state.2, state.1) =
      ((dramDifferentialSenseNominalClampedPairRate state).2,
        (dramDifferentialSenseNominalClampedPairRate state).1) := by
  rcases state with ⟨trueVoltage, complementVoltage⟩
  rfl

/-- A smooth clamped-field trajectory that starts strictly above the
metastable diagonal never meets or crosses it. The proof does not assume an
order invariant: it derives one from swap symmetry and global ODE uniqueness,
including uniqueness backward from a hypothetical crossing time. -/
theorem dramDifferentialSenseNominalClampedPairRate_strict_order
    {trajectory : ℝ → DramDifferentialSensePair}
    {initial : DramDifferentialSensePair}
    {horizon : ℝ}
    (hhorizon : 0 ≤ horizon)
    (hinitial : trajectory 0 = initial)
    (hinitialOrder : initial.2 < initial.1)
    (hsolution :
      ∀ time ∈ Set.Icc (0 : ℝ) horizon,
        HasDerivWithinAt trajectory
          (dramDifferentialSenseNominalClampedPairRate
            (trajectory time))
          (Set.Icc (0 : ℝ) horizon) time) :
    ∀ time ∈ Set.Icc (0 : ℝ) horizon,
      (trajectory time).2 < (trajectory time).1 := by
  have hcontinuous :
      ContinuousOn trajectory (Set.Icc (0 : ℝ) horizon) := by
    intro time htime
    exact (hsolution time htime).continuousWithinAt
  intro time htime
  by_contra hnotOrder
  have hreverse :
      (trajectory time).1 - (trajectory time).2 ≤ 0 := by
    linarith
  let difference : ℝ → ℝ :=
    fun point => (trajectory point).1 - (trajectory point).2
  have hdifferenceContinuous :
      ContinuousOn difference (Set.Icc (0 : ℝ) time) := by
    have hsubset :
        Set.Icc (0 : ℝ) time ⊆ Set.Icc (0 : ℝ) horizon := by
      intro point hpoint
      exact ⟨hpoint.1, hpoint.2.trans htime.2⟩
    exact
      ((continuous_fst.comp_continuousOn hcontinuous).sub
        (continuous_snd.comp_continuousOn hcontinuous)).mono hsubset
  have hinitialDifference :
      0 < difference 0 := by
    dsimp [difference]
    rw [hinitial]
    linarith
  have hzeroImage :
      (0 : ℝ) ∈
        difference '' Set.Icc (0 : ℝ) time := by
    apply intermediate_value_Icc' htime.1 hdifferenceContinuous
    constructor
    · simpa only [difference] using hreverse
    · exact hinitialDifference.le
  obtain ⟨crossing, hcrossingTime, hcrossing⟩ := hzeroImage
  have hcrossingEqual :
      trajectory crossing =
        ((trajectory crossing).2, (trajectory crossing).1) := by
    apply Prod.ext <;>
      dsimp [difference] at hcrossing ⊢ <;>
      linarith
  let swapped : ℝ → DramDifferentialSensePair :=
    fun point =>
      ((trajectory point).2, (trajectory point).1)
  have htrajectoryContinuous :
      ContinuousOn trajectory (Set.Icc (0 : ℝ) crossing) :=
    hcontinuous.mono
      (by
        intro point hpoint
        exact
          ⟨hpoint.1,
            hpoint.2.trans (hcrossingTime.2.trans htime.2)⟩)
  have hswappedContinuous :
      ContinuousOn swapped (Set.Icc (0 : ℝ) crossing) := by
    exact
      (continuous_snd.comp_continuousOn htrajectoryContinuous).prodMk
        (continuous_fst.comp_continuousOn htrajectoryContinuous)
  have htrajectoryLeftDerivative :
      ∀ point ∈ Set.Ioc (0 : ℝ) crossing,
        HasDerivWithinAt trajectory
          (dramDifferentialSenseNominalClampedPairRate
            (trajectory point))
          (Set.Iic point) point := by
    intro point hpoint
    have hpointHorizon :
        point ∈ Set.Ioc (0 : ℝ) horizon :=
      ⟨hpoint.1,
        hpoint.2.trans (hcrossingTime.2.trans htime.2)⟩
    exact
      ((hsolution point ⟨hpointHorizon.1.le, hpointHorizon.2⟩)
        |>.mono_of_mem_nhdsWithin
          (Icc_mem_nhdsLT_of_mem hpointHorizon)).Iic_of_Iio
  have hswappedLeftDerivative :
      ∀ point ∈ Set.Ioc (0 : ℝ) crossing,
        HasDerivWithinAt swapped
          (dramDifferentialSenseNominalClampedPairRate
            (swapped point))
          (Set.Iic point) point := by
    intro point hpoint
    have horiginal := htrajectoryLeftDerivative point hpoint
    have hswappedDerivative :
        HasDerivWithinAt swapped
          ((dramDifferentialSenseNominalClampedPairRate
              (trajectory point)).2,
            (dramDifferentialSenseNominalClampedPairRate
              (trajectory point)).1)
          (Set.Iic point) point :=
      (hasDerivWithinAt_snd_of_pair horiginal).prodMk
        (hasDerivWithinAt_fst_of_pair horiginal)
    simpa only [swapped,
      dramDifferentialSenseNominalClampedPairRate_swap] using
      hswappedDerivative
  have hequalOn :=
    ODE_solution_unique_of_mem_Icc_left
      (v := fun _point =>
        dramDifferentialSenseNominalClampedPairRate)
      (s := fun _point => Set.univ)
      (K := 10000000000000)
      (a := 0) (b := crossing)
      (fun _point _hpoint =>
        dramDifferentialSenseNominalClampedPairRate_lipschitz
          |>.lipschitzOnWith)
      htrajectoryContinuous htrajectoryLeftDerivative
      (fun _point _hpoint => Set.mem_univ _)
      hswappedContinuous hswappedLeftDerivative
      (fun _point _hpoint => Set.mem_univ _)
      hcrossingEqual
  have hatZero :
      trajectory 0 = swapped 0 :=
    hequalOn ⟨le_rfl, hcrossingTime.1⟩
  dsimp [swapped] at hatZero
  rw [hinitial] at hatZero
  have := congrArg Prod.fst hatZero
  dsimp at this
  linarith

private noncomputable def dramDifferentialSenseNominalProofWorld
    (initial : DramDifferentialSensePair) (horizon : ℝ) :
    DramDifferentialSenseWorld :=
  deterministicWorld nominalDramDifferentialSenseInstance
    { supply := 5
      initialTrue := initial.1
      initialComplement := initial.2
      horizon }

/-- Signed true/complement margin with fixed physical line identity. -/
def dramDifferentialSenseSignedPairMargin
    (value : Bool) (state : DramDifferentialSensePair) : ℝ :=
  if value then state.1 - state.2 else state.2 - state.1

/-- The signed margin is a continuous observation of the latch state. -/
theorem dramDifferentialSenseSignedPairMargin_continuous
    (value : Bool) :
    Continuous (dramDifferentialSenseSignedPairMargin value) := by
  cases value
  · change Continuous (fun state : DramDifferentialSensePair =>
      state.2 - state.1)
    exact continuous_snd.sub continuous_fst
  · change Continuous (fun state : DramDifferentialSensePair =>
      state.1 - state.2)
    exact continuous_fst.sub continuous_snd

/-- Time derivative of the signed margin under the exact nominal proof
field. -/
noncomputable def dramDifferentialSenseSignedPairRate
    (value : Bool) (state : DramDifferentialSensePair) : ℝ :=
  let rate := dramDifferentialSenseNominalClampedPairRate state
  if value then rate.1 - rate.2 else rate.2 - rate.1

/-- The signed-margin rate is continuous over the whole pair state space. -/
theorem dramDifferentialSenseSignedPairRate_continuous
    (value : Bool) :
    Continuous (dramDifferentialSenseSignedPairRate value) := by
  have hfield :=
    dramDifferentialSenseNominalClampedPairRate_lipschitz.continuous
  cases value
  · have hcontinuous :=
      (continuous_snd.comp hfield).sub
        (continuous_fst.comp hfield)
    change Continuous (fun state : DramDifferentialSensePair =>
      (dramDifferentialSenseNominalClampedPairRate state).2 -
        (dramDifferentialSenseNominalClampedPairRate state).1) at hcontinuous
    exact hcontinuous
  · have hcontinuous :=
      (continuous_fst.comp hfield).sub
        (continuous_snd.comp hfield)
    change Continuous (fun state : DramDifferentialSensePair =>
      (dramDifferentialSenseNominalClampedPairRate state).1 -
        (dramDifferentialSenseNominalClampedPairRate state).2) at hcontinuous
    exact hcontinuous

/-- The derivative of the signed margin is the signed observation of the
nominal pair field. -/
theorem dramDifferentialSenseSignedPairMargin_hasDerivWithinAt
    (value : Bool)
    {trajectory : ℝ → DramDifferentialSensePair}
    {time : ℝ} {set : Set ℝ}
    (htrajectory :
      HasDerivWithinAt trajectory
        (dramDifferentialSenseNominalClampedPairRate
          (trajectory time))
        set time) :
    HasDerivWithinAt
      (fun point =>
        dramDifferentialSenseSignedPairMargin value
          (trajectory point))
      (dramDifferentialSenseSignedPairRate value
        (trajectory time))
      set time := by
  cases value
  · change
      HasDerivWithinAt
        (fun point => (trajectory point).2 - (trajectory point).1)
        ((dramDifferentialSenseNominalClampedPairRate
              (trajectory time)).2 -
          (dramDifferentialSenseNominalClampedPairRate
              (trajectory time)).1)
        set time
    exact
      (hasDerivWithinAt_snd_of_pair htrajectory).sub
        (hasDerivWithinAt_fst_of_pair htrajectory)
  · change
      HasDerivWithinAt
        (fun point => (trajectory point).1 - (trajectory point).2)
        ((dramDifferentialSenseNominalClampedPairRate
              (trajectory time)).1 -
          (dramDifferentialSenseNominalClampedPairRate
              (trajectory time)).2)
        set time
    exact
      (hasDerivWithinAt_fst_of_pair htrajectory).sub
        (hasDerivWithinAt_snd_of_pair htrajectory)

/-- In the nominal rail square, a nonnegative signed differential has a
nonnegative signed derivative under the exact proof field. Strictly ordered
nonterminal states use the primitive MOS current-order theorem; the diagonal
and the resolved rail endpoint are handled exactly. -/
theorem
    dramDifferentialSenseNominalClampedPairRate_difference_nonnegative
    {state : DramDifferentialSensePair}
    (hdomain :
      state.1 ∈ Set.Icc (0 : ℝ) 5 ∧
        state.2 ∈ Set.Icc (0 : ℝ) 5)
    (horder : state.2 ≤ state.1) :
    0 ≤
      (dramDifferentialSenseNominalClampedPairRate state).1 -
        (dramDifferentialSenseNominalClampedPairRate state).2 := by
  rcases state with ⟨trueVoltage, complementVoltage⟩
  dsimp only at hdomain horder ⊢
  rcases lt_or_eq_of_le horder with hstrict | hequal
  · by_cases hnotRail : trueVoltage < 5 ∨ 0 < complementVoltage
    · let world :=
        dramDifferentialSenseNominalProofWorld
          (trueVoltage, complementVoltage) 0
      have hresidual :
          dramDifferentialSenseDAE.residual world 0
            (dramDifferentialSensePairState
              (trueVoltage, complementVoltage))
            (dramDifferentialSensePairState
              (dramDifferentialSenseNominalClampedPairRate
                (trueVoltage, complementVoltage))) := by
        apply
          dramDifferentialSenseNominalClampedPairRate_residual
            (world := world)
        · rfl
        · rfl
        · exact
            ⟨hdomain.1.1, hdomain.1.2,
              hdomain.2.1, hdomain.2.2⟩
      have hstateDomain :
          DramDifferentialSenseStateInRailDomain world
            (dramDifferentialSensePairState
              (trueVoltage, complementVoltage)) := by
        exact
          ⟨hdomain.1.1, hdomain.1.2,
            hdomain.2.1, hdomain.2.2⟩
      exact
        (dramDifferentialSense_nominal_unbalanced_regeneration
          (world := world) rfl rfl hstateDomain hstrict hnotRail
          hresidual).le
    · push Not at hnotRail
      have htrue : trueVoltage = 5 := by
        linarith [hdomain.1.2]
      have hcomplement : complementVoltage = 0 := by
        linarith [hdomain.2.1]
      subst trueVoltage
      subst complementVoltage
      have hclamp0 : dramSenseVoltageClamp 0 = 0 :=
        dramSenseVoltageClamp_eq (by norm_num) (by norm_num)
      have hclamp5 : dramSenseVoltageClamp 5 = 5 :=
        dramSenseVoltageClamp_eq (by norm_num) (by norm_num)
      have hzeroGate :
          dramDifferentialSenseClampedNCurrent 0 5 = 0 := by
        unfold dramDifferentialSenseClampedNCurrent
        rw [dramSenseReluSquare_eq_max_sq (by norm_num),
          dramSenseReluSquare_eq_max_sq (by norm_num)]
        norm_num
      simp only [dramDifferentialSenseNominalClampedPairRate,
        hclamp0, hclamp5, sub_self, sub_zero,
        dramDifferentialSenseClampedNCurrent_zero_output,
        hzeroGate, zero_div]
      norm_num
  · subst complementVoltage
    have hswap :=
      dramDifferentialSenseNominalClampedPairRate_swap
        (trueVoltage, trueVoltage)
    have hcomponents := congrArg Prod.fst hswap
    dsimp at hcomponents
    linarith

/-- Strict form of the nominal field direction theorem. -/
theorem
    dramDifferentialSenseNominalClampedPairRate_difference_positive
    {state : DramDifferentialSensePair}
    (hdomain :
      state.1 ∈ Set.Icc (0 : ℝ) 5 ∧
        state.2 ∈ Set.Icc (0 : ℝ) 5)
    (horder : state.2 < state.1)
    (hnotRail : state.1 < 5 ∨ 0 < state.2) :
    0 <
      (dramDifferentialSenseNominalClampedPairRate state).1 -
        (dramDifferentialSenseNominalClampedPairRate state).2 := by
  let world :=
    dramDifferentialSenseNominalProofWorld state 0
  have hresidual :
      dramDifferentialSenseDAE.residual world 0
        (dramDifferentialSensePairState state)
        (dramDifferentialSensePairState
          (dramDifferentialSenseNominalClampedPairRate state)) := by
    apply
      dramDifferentialSenseNominalClampedPairRate_residual
        (world := world)
    · rfl
    · rfl
    · exact
        ⟨hdomain.1.1, hdomain.1.2,
          hdomain.2.1, hdomain.2.2⟩
  have hstateDomain :
      DramDifferentialSenseStateInRailDomain world
        (dramDifferentialSensePairState state) :=
    ⟨hdomain.1.1, hdomain.1.2,
      hdomain.2.1, hdomain.2.2⟩
  exact
    dramDifferentialSense_nominal_unbalanced_regeneration
      (world := world) rfl rfl hstateDomain horder hnotRail hresidual

/-- Every rail-valid state with positive but unresolved signed margin has a
strictly positive signed-margin rate. -/
theorem dramDifferentialSenseSignedPairRate_positive
    {value : Bool} {state : DramDifferentialSensePair}
    (hdomain :
      state.1 ∈ Set.Icc (0 : ℝ) 5 ∧
        state.2 ∈ Set.Icc (0 : ℝ) 5)
    (hmarginPositive :
      0 < dramDifferentialSenseSignedPairMargin value state)
    (hmarginUnresolved :
      dramDifferentialSenseSignedPairMargin value state < 5) :
    0 < dramDifferentialSenseSignedPairRate value state := by
  cases hvalue : value
  · simp only [hvalue, Bool.false_eq_true, if_false,
      dramDifferentialSenseSignedPairMargin] at hmarginPositive hmarginUnresolved
    have hnotRail : state.2 < 5 ∨ 0 < state.1 := by
      by_contra hnot
      push Not at hnot
      have hcomplement : state.2 = 5 := by
        linarith [hdomain.2.2]
      have htrue : state.1 = 0 := by
        linarith [hdomain.1.1]
      linarith
    have horder : (state.2, state.1).2 < (state.2, state.1).1 := by
      dsimp only
      linarith
    have hpositive :=
      dramDifferentialSenseNominalClampedPairRate_difference_positive
        (state := (state.2, state.1))
        ⟨hdomain.2, hdomain.1⟩ horder hnotRail
    rw [dramDifferentialSenseNominalClampedPairRate_swap] at hpositive
    change
      0 <
        (dramDifferentialSenseNominalClampedPairRate state).2 -
          (dramDifferentialSenseNominalClampedPairRate state).1
    exact hpositive
  · simp only [hvalue, if_true,
      dramDifferentialSenseSignedPairMargin] at hmarginPositive hmarginUnresolved
    have hnotRail : state.1 < 5 ∨ 0 < state.2 := by
      by_contra hnot
      push Not at hnot
      have htrue : state.1 = 5 := by
        linarith [hdomain.1.2]
      have hcomplement : state.2 = 0 := by
        linarith [hdomain.2.1]
      linarith
    change
      0 <
        (dramDifferentialSenseNominalClampedPairRate state).1 -
          (dramDifferentialSenseNominalClampedPairRate state).2
    have horder : state.2 < state.1 := by
      linarith
    exact
      dramDifferentialSenseNominalClampedPairRate_difference_positive
        hdomain horder hnotRail

/-- Compact rail-valid region between a delivered signed margin and a
requested resolution margin. -/
noncomputable def dramDifferentialSenseResolutionRegion
    (value : Bool) (delivered required : ℝ) :
    Set DramDifferentialSensePair :=
  (Set.Icc (0 : ℝ) 5 ×ˢ Set.Icc (0 : ℝ) 5) ∩
    dramDifferentialSenseSignedPairMargin value ⁻¹'
      Set.Icc delivered required

theorem dramDifferentialSenseResolutionRegion_isCompact
    (value : Bool) (delivered required : ℝ) :
    IsCompact
      (dramDifferentialSenseResolutionRegion
        value delivered required) := by
  apply (isCompact_Icc.prod isCompact_Icc).inter_right
  exact
    isClosed_Icc.preimage
      (dramDifferentialSenseSignedPairMargin_continuous value)

/-- A positive delivered margin and any target below the rail separation
admit a uniform positive regeneration-rate certificate over every
rail-valid unresolved common-mode state. -/
theorem dramDifferentialSense_exists_uniform_resolution_rate
    (value : Bool) {delivered required : ℝ}
    (hdelivered : 0 < delivered)
    (hrequired : required < 5) :
    ∃ minimumRate : ℝ,
      0 < minimumRate ∧
      ∀ state,
        state ∈
            dramDifferentialSenseResolutionRegion
              value delivered required →
          minimumRate ≤
            dramDifferentialSenseSignedPairRate value state := by
  apply
    (dramDifferentialSenseResolutionRegion_isCompact
      value delivered required).exists_forall_le'
  · exact
      dramDifferentialSenseSignedPairRate_continuous
        value |>.continuousOn
  · intro state hstate
    exact
      dramDifferentialSenseSignedPairRate_positive
        ⟨hstate.1.1, hstate.1.2⟩
        (hdelivered.trans_le hstate.2.1)
        (hstate.2.2.trans_lt hrequired)

/-- Along every constructed smooth nominal trajectory that begins with a
positive true-minus-complement margin, that margin is monotone
nondecreasing. This rules out droop, polarity reversal, and a transient
return toward metastability; it does not yet provide a quantitative
resolution deadline. -/
theorem
    dramDifferentialSenseNominalClampedPairRate_difference_monotone
    {trajectory : ℝ → DramDifferentialSensePair}
    {initial : DramDifferentialSensePair}
    {horizon : ℝ}
    (hhorizon : 0 ≤ horizon)
    (hinitial : trajectory 0 = initial)
    (hinitialTrue : initial.1 ∈ Set.Icc (0 : ℝ) 5)
    (hinitialComplement : initial.2 ∈ Set.Icc (0 : ℝ) 5)
    (hinitialOrder : initial.2 < initial.1)
    (hsolution :
      ∀ time ∈ Set.Icc (0 : ℝ) horizon,
        HasDerivWithinAt trajectory
          (dramDifferentialSenseNominalClampedPairRate
            (trajectory time))
          (Set.Icc (0 : ℝ) horizon) time) :
    MonotoneOn
      (fun time =>
        (trajectory time).1 - (trajectory time).2)
      (Set.Icc (0 : ℝ) horizon) := by
  have hinvariant :=
    dramDifferentialSenseNominalClampedPairRate_invariant
      hhorizon hinitial hinitialTrue hinitialComplement hsolution
  have hstrictOrder :=
    dramDifferentialSenseNominalClampedPairRate_strict_order
      hhorizon hinitial hinitialOrder hsolution
  have hcontinuous :
      ContinuousOn trajectory (Set.Icc (0 : ℝ) horizon) := by
    intro time htime
    exact (hsolution time htime).continuousWithinAt
  have hdifferenceContinuous :
      ContinuousOn
        (fun time =>
          (trajectory time).1 - (trajectory time).2)
        (Set.Icc (0 : ℝ) horizon) :=
    (continuous_fst.comp_continuousOn hcontinuous).sub
      (continuous_snd.comp_continuousOn hcontinuous)
  apply monotoneOn_of_hasDerivWithinAt_nonneg
    (convex_Icc (0 : ℝ) horizon) hdifferenceContinuous
  · intro time htime
    have hpair :=
      (hsolution time (interior_subset htime)).mono
        interior_subset
    exact
      (hasDerivWithinAt_fst_of_pair hpair).sub
        (hasDerivWithinAt_snd_of_pair hpair)
  · intro time htime
    have hclosed := interior_subset htime
    exact
      dramDifferentialSenseNominalClampedPairRate_difference_nonnegative
        (hinvariant time hclosed)
        (hstrictOrder time hclosed).le

/-- A uniform positive rate certificate gives an explicit finite resolution
deadline. The proof is by contradiction: before the target is reached,
monotonicity keeps the trajectory inside the certified compact region, so
the signed margin grows at least `minimumRate * time`. -/
theorem dramDifferentialSenseSignedPairMargin_reaches_of_rate_certificate
    {value : Bool}
    {trajectory : ℝ → DramDifferentialSensePair}
    {initial : DramDifferentialSensePair}
    {horizon delivered required minimumRate deadline : ℝ}
    (hhorizon : 0 ≤ horizon)
    (hinitial : trajectory 0 = initial)
    (hsolution :
      ∀ time ∈ Set.Icc (0 : ℝ) horizon,
        HasDerivWithinAt trajectory
          (dramDifferentialSenseNominalClampedPairRate
            (trajectory time))
          (Set.Icc (0 : ℝ) horizon) time)
    (hinvariant :
      ∀ time ∈ Set.Icc (0 : ℝ) horizon,
        (trajectory time).1 ∈ Set.Icc (0 : ℝ) 5 ∧
          (trajectory time).2 ∈ Set.Icc (0 : ℝ) 5)
    (hmonotone :
      MonotoneOn
        (fun time =>
          dramDifferentialSenseSignedPairMargin value
            (trajectory time))
        (Set.Icc (0 : ℝ) horizon))
    (hdelivered :
      delivered ≤
        dramDifferentialSenseSignedPairMargin value initial)
    (hminimumRate : 0 < minimumRate)
    (hrate :
      ∀ state,
        state ∈
            dramDifferentialSenseResolutionRegion
              value delivered required →
          minimumRate ≤
            dramDifferentialSenseSignedPairRate value state)
    (hdeadline0 : 0 ≤ deadline)
    (hdeadlineHorizon : deadline ≤ horizon)
    (hdeadline :
      required - delivered ≤ minimumRate * deadline) :
    required ≤
      dramDifferentialSenseSignedPairMargin value
        (trajectory deadline) := by
  by_contra hnotReached
  have hdeadlineBelow :
      dramDifferentialSenseSignedPairMargin value
          (trajectory deadline) < required :=
    lt_of_not_ge hnotReached
  let margin : ℝ → ℝ := fun time =>
    dramDifferentialSenseSignedPairMargin value
      (trajectory time)
  let progress : ℝ → ℝ := fun time =>
    margin time - minimumRate * time
  have hsubset :
      Set.Icc (0 : ℝ) deadline ⊆ Set.Icc (0 : ℝ) horizon := by
    intro time htime
    exact ⟨htime.1, htime.2.trans hdeadlineHorizon⟩
  have htrajectoryContinuous :
      ContinuousOn trajectory (Set.Icc (0 : ℝ) deadline) := by
    apply ContinuousOn.mono _ hsubset
    intro time htime
    exact (hsolution time htime).continuousWithinAt
  have hmarginContinuous :
      ContinuousOn margin (Set.Icc (0 : ℝ) deadline) := by
    exact
      dramDifferentialSenseSignedPairMargin_continuous value
        |>.continuousOn.comp htrajectoryContinuous
          (fun _time _htime => Set.mem_univ _)
  have hprogressContinuous :
      ContinuousOn progress (Set.Icc (0 : ℝ) deadline) := by
    exact
      hmarginContinuous.sub
        (continuous_const.mul continuous_id).continuousOn
  have hprogressMonotone :
      MonotoneOn progress (Set.Icc (0 : ℝ) deadline) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg
      (convex_Icc (0 : ℝ) deadline) hprogressContinuous
    · intro time htime
      have htimeClosed : time ∈ Set.Icc (0 : ℝ) deadline :=
        interior_subset htime
      have hpair :=
        (hsolution time (hsubset htimeClosed)).mono hsubset
      have hmarginDerivative :=
        dramDifferentialSenseSignedPairMargin_hasDerivWithinAt
          value (hpair.mono interior_subset)
      have hlinearDerivative :
          HasDerivWithinAt (fun point : ℝ => minimumRate * point)
            minimumRate (interior (Set.Icc (0 : ℝ) deadline)) time :=
        by
          simpa only [id_eq, mul_one] using
            ((hasDerivAt_id time).const_mul
              minimumRate).hasDerivWithinAt
      exact hmarginDerivative.sub hlinearDerivative
    · intro time htime
      have htimeClosed : time ∈ Set.Icc (0 : ℝ) deadline :=
        interior_subset htime
      have htimeHorizon := hsubset htimeClosed
      have hmarginFromInitial :
          dramDifferentialSenseSignedPairMargin value initial ≤
            margin time := by
        rw [← hinitial]
        exact
          hmonotone ⟨le_rfl, hhorizon⟩ htimeHorizon htimeClosed.1
      have hmarginBeforeDeadline :
          margin time ≤ margin deadline :=
        hmonotone htimeHorizon
          ⟨hdeadline0, hdeadlineHorizon⟩ htimeClosed.2
      have hstateRegion :
          trajectory time ∈
            dramDifferentialSenseResolutionRegion
              value delivered required := by
        exact
          ⟨hinvariant time htimeHorizon,
            ⟨hdelivered.trans hmarginFromInitial,
              hmarginBeforeDeadline.trans hdeadlineBelow.le⟩⟩
      exact sub_nonneg.mpr (hrate (trajectory time) hstateRegion)
  have hprogressGrowth :
      progress 0 ≤ progress deadline :=
    hprogressMonotone
      ⟨le_rfl, hdeadline0⟩
      ⟨hdeadline0, le_rfl⟩ hdeadline0
  dsimp only [progress, margin] at hprogressGrowth
  rw [hinitial] at hprogressGrowth
  nlinarith

/-- Source-derived finite resolution certificate for a smooth nominal
trajectory. The returned rate is the positive compact-region minimum, and
the displayed quotient is the corresponding conservative deadline. -/
theorem dramDifferentialSenseSignedPairMargin_resolution_certificate
    {value : Bool}
    {trajectory : ℝ → DramDifferentialSensePair}
    {initial : DramDifferentialSensePair}
    {horizon delivered required : ℝ}
    (hhorizon : 0 ≤ horizon)
    (hinitial : trajectory 0 = initial)
    (hsolution :
      ∀ time ∈ Set.Icc (0 : ℝ) horizon,
        HasDerivWithinAt trajectory
          (dramDifferentialSenseNominalClampedPairRate
            (trajectory time))
          (Set.Icc (0 : ℝ) horizon) time)
    (hinvariant :
      ∀ time ∈ Set.Icc (0 : ℝ) horizon,
        (trajectory time).1 ∈ Set.Icc (0 : ℝ) 5 ∧
          (trajectory time).2 ∈ Set.Icc (0 : ℝ) 5)
    (hmonotone :
      MonotoneOn
        (fun time =>
          dramDifferentialSenseSignedPairMargin value
            (trajectory time))
        (Set.Icc (0 : ℝ) horizon))
    (hdeliveredPositive : 0 < delivered)
    (hdeliveredInitial :
      delivered ≤
        dramDifferentialSenseSignedPairMargin value initial)
    (hdeliveredRequired : delivered ≤ required)
    (hrequired : required < 5) :
    ∃ minimumRate : ℝ,
      0 < minimumRate ∧
      let deadline := (required - delivered) / minimumRate
      0 ≤ deadline ∧
        (deadline ≤ horizon →
          required ≤
            dramDifferentialSenseSignedPairMargin value
              (trajectory deadline)) := by
  obtain ⟨minimumRate, hminimumRate, hrate⟩ :=
    dramDifferentialSense_exists_uniform_resolution_rate
      value hdeliveredPositive hrequired
  refine ⟨minimumRate, hminimumRate, ?_⟩
  dsimp only
  have hdeadline0 :
      0 ≤ (required - delivered) / minimumRate :=
    div_nonneg (sub_nonneg.mpr hdeliveredRequired) hminimumRate.le
  refine ⟨hdeadline0, ?_⟩
  intro hdeadlineHorizon
  apply
    dramDifferentialSenseSignedPairMargin_reaches_of_rate_certificate
      hhorizon hinitial hsolution hinvariant hmonotone
      hdeliveredInitial hminimumRate hrate hdeadline0
      hdeadlineHorizon
  have hdeadlineIdentity :
      minimumRate * ((required - delivered) / minimumRate) =
        required - delivered := by
    field_simp [hminimumRate.ne']
  rw [hdeadlineIdentity]

/-- The globally clamped nominal two-node field has a unique smooth solution
on every finite horizon. The subsequent theorem lifts this solver-friendly
capability to the actual almost-everywhere `ACBehavesOn` semantics. -/
theorem dramDifferentialSenseNominalClampedPairRate_determinate
    {first second : ℝ → DramDifferentialSensePair}
    {horizon : ℝ}
    (hfirst :
      ∀ time ∈ Set.Icc (0 : ℝ) horizon,
        HasDerivWithinAt first
          (dramDifferentialSenseNominalClampedPairRate (first time))
          (Set.Icc (0 : ℝ) horizon) time)
    (hsecond :
      ∀ time ∈ Set.Icc (0 : ℝ) horizon,
        HasDerivWithinAt second
          (dramDifferentialSenseNominalClampedPairRate (second time))
          (Set.Icc (0 : ℝ) horizon) time)
    (hinitial : first 0 = second 0) :
    Set.EqOn first second (Set.Icc (0 : ℝ) horizon) := by
  have hfirstContinuous :
      ContinuousOn first (Set.Icc (0 : ℝ) horizon) := by
    intro time htime
    exact (hfirst time htime).continuousWithinAt
  have hsecondContinuous :
      ContinuousOn second (Set.Icc (0 : ℝ) horizon) := by
    intro time htime
    exact (hsecond time htime).continuousWithinAt
  have hfirstRight :
      ∀ time ∈ Set.Ico (0 : ℝ) horizon,
        HasDerivWithinAt first
          (dramDifferentialSenseNominalClampedPairRate (first time))
          (Set.Ici time) time := by
    intro time htime
    exact
      ((hfirst time ⟨htime.1, htime.2.le⟩)
        |>.mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGT_of_mem htime)).Ici_of_Ioi
  have hsecondRight :
      ∀ time ∈ Set.Ico (0 : ℝ) horizon,
        HasDerivWithinAt second
          (dramDifferentialSenseNominalClampedPairRate (second time))
          (Set.Ici time) time := by
    intro time htime
    exact
      ((hsecond time ⟨htime.1, htime.2.le⟩)
        |>.mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGT_of_mem htime)).Ici_of_Ioi
  exact
    ODE_solution_unique
      (v := fun _time =>
        dramDifferentialSenseNominalClampedPairRate)
      (K := 10000000000000)
      (fun _time =>
        dramDifferentialSenseNominalClampedPairRate_lipschitz)
      hfirstContinuous hfirstRight
      hsecondContinuous hsecondRight hinitial

/-- Any two absolutely-continuous behaviors of the primitive nominal latch
with the same initial state coincide throughout a shared rail-valid horizon.
This is determinacy of the actual a.e. DAE semantics, not only of the smooth
proof capability. -/
theorem dramDifferentialSense_nominal_unbalanced_determinate_on_domain
    {world : DramDifferentialSenseWorld}
    {first second : VectorTrace DramDifferentialSenseIndex}
    {horizon : ℝ}
    (hsupply : world.environment.supply = 5)
    (hinstance :
      world.fabricated = nominalDramDifferentialSenseInstance)
    (hfirst :
      dramDifferentialSenseDAE.ACBehavesOn world horizon first)
    (hsecond :
      dramDifferentialSenseDAE.ACBehavesOn world horizon second)
    (hfirstDomain :
      ∀ point ∈ Set.Icc (0 : ℝ) horizon,
        DramDifferentialSenseStateInRailDomain world (first point))
    (hsecondDomain :
      ∀ point ∈ Set.Icc (0 : ℝ) horizon,
        DramDifferentialSenseStateInRailDomain world (second point))
    (hinitial : first 0 = second 0) :
    Set.EqOn first second (Set.Icc (0 : ℝ) horizon) := by
  let firstPair : ℝ → DramDifferentialSensePair :=
    fun point => dramDifferentialSenseStatePair (first point)
  let secondPair : ℝ → DramDifferentialSensePair :=
    fun point => dramDifferentialSenseStatePair (second point)
  have hfirstSolution :
      ∀ point ∈ Set.Icc (0 : ℝ) horizon,
        HasDerivWithinAt firstPair
          (dramDifferentialSenseNominalClampedPairRate
            (firstPair point))
          (Set.Icc (0 : ℝ) horizon) point := by
    intro point hpoint
    exact
      dramDifferentialSenseNominalClampedPairRate_hasDerivWithinAt
        hsupply hinstance hfirst hfirstDomain hpoint
  have hsecondSolution :
      ∀ point ∈ Set.Icc (0 : ℝ) horizon,
        HasDerivWithinAt secondPair
          (dramDifferentialSenseNominalClampedPairRate
            (secondPair point))
          (Set.Icc (0 : ℝ) horizon) point := by
    intro point hpoint
    exact
      dramDifferentialSenseNominalClampedPairRate_hasDerivWithinAt
        hsupply hinstance hsecond hsecondDomain hpoint
  have hinitialPair : firstPair 0 = secondPair 0 := by
    dsimp only [firstPair, secondPair]
    rw [hinitial]
  have hpairs :=
    dramDifferentialSenseNominalClampedPairRate_determinate
      hfirstSolution hsecondSolution hinitialPair
  intro point hpoint
  have hpairEqual : firstPair point = secondPair point :=
    hpairs hpoint
  have hstateEqual :=
    congrArg dramDifferentialSensePairState hpairEqual
  simpa only [firstPair, secondPair,
    dramDifferentialSensePairState_statePair] using hstateEqual

/-- Behavior-level determinacy: any two source-program behaviors with the
same world coincide throughout a horizon on which both stay inside the
declared rail-validity domain. Their initial equality is derived from the two
initial-condition equations in `DramDifferentialSenseProgram`. -/
theorem dramDifferentialSense_nominal_behavior_determinate_on_domain
    {world : DramDifferentialSenseWorld}
    {first second : DramDifferentialSenseBoundary}
    (hsupply : world.environment.supply = 5)
    (hinstance :
      world.fabricated = nominalDramDifferentialSenseInstance)
    (hfirst : DramDifferentialSenseBehavior world first ())
    (hsecond : DramDifferentialSenseBehavior world second ())
    (hfirstDomain :
      ∀ point ∈ Set.Icc (0 : ℝ) world.environment.horizon,
        DramDifferentialSenseStateInRailDomain world
          (first.voltage point))
    (hsecondDomain :
      ∀ point ∈ Set.Icc (0 : ℝ) world.environment.horizon,
        DramDifferentialSenseStateInRailDomain world
          (second.voltage point)) :
    Set.EqOn first.voltage second.voltage
      (Set.Icc (0 : ℝ) world.environment.horizon) := by
  have hinitial : first.voltage 0 = second.voltage 0 := by
    funext index
    cases index
    · exact
        (hfirst .initialTrue).trans
          (hsecond .initialTrue).symm
    · exact
        (hfirst .initialComplement).trans
          (hsecond .initialComplement).symm
  exact
    dramDifferentialSense_nominal_unbalanced_determinate_on_domain
      hsupply hinstance
      (hfirst .evolution) (hsecond .evolution)
      hfirstDomain hsecondDomain hinitial

/-- Non-vacuous smooth realizability with the two core transient safety
properties returned outside the equations: rail-domain closure and
nondecreasing signed voltage margin. -/
theorem
    dramDifferentialSenseNominalClampedPairRate_realizable_monotone
    (initial : DramDifferentialSensePair)
    {horizon : ℝ}
    (hhorizon : 0 ≤ horizon)
    (hinitialTrue : initial.1 ∈ Set.Icc (0 : ℝ) 5)
    (hinitialComplement : initial.2 ∈ Set.Icc (0 : ℝ) 5)
    (hinitialOrder : initial.2 < initial.1) :
    ∃ trajectory : ℝ → DramDifferentialSensePair,
      trajectory 0 = initial ∧
      (∀ time ∈ Set.Icc (0 : ℝ) horizon,
        HasDerivWithinAt trajectory
          (dramDifferentialSenseNominalClampedPairRate
            (trajectory time))
          (Set.Icc (0 : ℝ) horizon) time) ∧
      (∀ time ∈ Set.Icc (0 : ℝ) horizon,
        (trajectory time).1 ∈ Set.Icc (0 : ℝ) 5 ∧
          (trajectory time).2 ∈ Set.Icc (0 : ℝ) 5) ∧
      MonotoneOn
        (fun time =>
          (trajectory time).1 - (trajectory time).2)
        (Set.Icc (0 : ℝ) horizon) := by
  obtain ⟨trajectory, hinitial, hsolution⟩ :=
    dramDifferentialSenseNominalClampedPairRate_realizable
      initial hhorizon
  have hinvariant :=
    dramDifferentialSenseNominalClampedPairRate_invariant
      hhorizon hinitial hinitialTrue hinitialComplement hsolution
  have hmonotone :=
    dramDifferentialSenseNominalClampedPairRate_difference_monotone
      hhorizon hinitial hinitialTrue hinitialComplement
      hinitialOrder hsolution
  exact
    ⟨trajectory, hinitial, hsolution, hinvariant, hmonotone⟩

/-- Both polarities have an inhabited smooth nominal trajectory whose signed
logic margin never decreases. The false case is proved by applying the same
theorem to the swapped trajectory; physical line identity in the returned
trajectory is unchanged. -/
theorem
    dramDifferentialSenseNominalClampedPairRate_realizable_signed_monotone
    (value : Bool)
    (initial : DramDifferentialSensePair)
    {horizon : ℝ}
    (hhorizon : 0 ≤ horizon)
    (hinitialTrue : initial.1 ∈ Set.Icc (0 : ℝ) 5)
    (hinitialComplement : initial.2 ∈ Set.Icc (0 : ℝ) 5)
    (hinitialOrder :
      if value then initial.2 < initial.1
      else initial.1 < initial.2) :
    ∃ trajectory : ℝ → DramDifferentialSensePair,
      trajectory 0 = initial ∧
      (∀ time ∈ Set.Icc (0 : ℝ) horizon,
        HasDerivWithinAt trajectory
          (dramDifferentialSenseNominalClampedPairRate
            (trajectory time))
          (Set.Icc (0 : ℝ) horizon) time) ∧
      (∀ time ∈ Set.Icc (0 : ℝ) horizon,
        (trajectory time).1 ∈ Set.Icc (0 : ℝ) 5 ∧
          (trajectory time).2 ∈ Set.Icc (0 : ℝ) 5) ∧
      MonotoneOn
        (fun time =>
          dramDifferentialSenseSignedPairMargin value
            (trajectory time))
        (Set.Icc (0 : ℝ) horizon) := by
  obtain ⟨trajectory, hinitial, hsolution⟩ :=
    dramDifferentialSenseNominalClampedPairRate_realizable
      initial hhorizon
  have hinvariant :=
    dramDifferentialSenseNominalClampedPairRate_invariant
      hhorizon hinitial hinitialTrue hinitialComplement hsolution
  cases hvalue : value
  · simp only [hvalue, Bool.false_eq_true, if_false] at hinitialOrder
    let swapped : ℝ → DramDifferentialSensePair :=
      fun time => ((trajectory time).2, (trajectory time).1)
    have hswappedInitial :
        swapped 0 = (initial.2, initial.1) := by
      dsimp [swapped]
      rw [hinitial]
    have hswappedSolution :
        ∀ time ∈ Set.Icc (0 : ℝ) horizon,
          HasDerivWithinAt swapped
            (dramDifferentialSenseNominalClampedPairRate
              (swapped time))
            (Set.Icc (0 : ℝ) horizon) time := by
      intro time htime
      have horiginal := hsolution time htime
      have hswappedDerivative :
          HasDerivWithinAt swapped
            ((dramDifferentialSenseNominalClampedPairRate
                (trajectory time)).2,
              (dramDifferentialSenseNominalClampedPairRate
                (trajectory time)).1)
            (Set.Icc (0 : ℝ) horizon) time :=
        (hasDerivWithinAt_snd_of_pair horiginal).prodMk
          (hasDerivWithinAt_fst_of_pair horiginal)
      simpa only [swapped,
        dramDifferentialSenseNominalClampedPairRate_swap] using
        hswappedDerivative
    have hmonotone :=
      dramDifferentialSenseNominalClampedPairRate_difference_monotone
        hhorizon hswappedInitial
        hinitialComplement hinitialTrue hinitialOrder
        hswappedSolution
    refine ⟨trajectory, hinitial, hsolution, hinvariant, ?_⟩
    simpa [hvalue, dramDifferentialSenseSignedPairMargin,
      swapped] using hmonotone
  · simp only [hvalue, if_true] at hinitialOrder
    have hmonotone :=
      dramDifferentialSenseNominalClampedPairRate_difference_monotone
        hhorizon hinitial hinitialTrue hinitialComplement
        hinitialOrder hsolution
    refine ⟨trajectory, hinitial, hsolution, hinvariant, ?_⟩
    simpa [hvalue, dramDifferentialSenseSignedPairMargin] using
      hmonotone

/-- Bundled non-vacuous resolution witness. Its trajectory satisfies both
the globally Lipschitz proof field and the primitive source DAE; safety and
the finite-target deadline remain inspectable fields. -/
structure DramDifferentialSenseResolutionWitness
    (world : DramDifferentialSenseWorld)
    (value : Bool)
    (initial : DramDifferentialSensePair)
    (required : ℝ) where
  trajectory : ℝ → DramDifferentialSensePair
  initial_eq : trajectory 0 = initial
  solution :
    ∀ time ∈ Set.Icc (0 : ℝ) world.environment.horizon,
      HasDerivWithinAt trajectory
        (dramDifferentialSenseNominalClampedPairRate
          (trajectory time))
        (Set.Icc (0 : ℝ) world.environment.horizon) time
  invariant :
    ∀ time ∈ Set.Icc (0 : ℝ) world.environment.horizon,
      (trajectory time).1 ∈ Set.Icc (0 : ℝ) 5 ∧
        (trajectory time).2 ∈ Set.Icc (0 : ℝ) 5
  margin_monotone :
    MonotoneOn
      (fun time =>
        dramDifferentialSenseSignedPairMargin value
          (trajectory time))
      (Set.Icc (0 : ℝ) world.environment.horizon)
  primitive_residual :
    ∀ time ∈ Set.Icc (0 : ℝ) world.environment.horizon,
      dramDifferentialSenseDAE.residual world time
        (dramDifferentialSensePairState (trajectory time))
        (dramDifferentialSensePairState
          (dramDifferentialSenseNominalClampedPairRate
            (trajectory time)))
  minimumRate : ℝ
  minimumRate_pos : 0 < minimumRate
  deadline_nonnegative :
    0 ≤
      (required -
          dramDifferentialSenseSignedPairMargin value initial) /
        minimumRate
  resolves_by_deadline :
    let deadline :=
      (required -
          dramDifferentialSenseSignedPairMargin value initial) /
        minimumRate
    deadline ≤ world.environment.horizon →
      required ≤
        dramDifferentialSenseSignedPairMargin value
          (trajectory deadline)

/-- Every strictly ordered nominal initial state in the rail square has a
source-DAE resolution witness for every requested margin between its
delivered margin and full rail separation. -/
theorem dramDifferentialSense_nominal_resolution_realizable
    {world : DramDifferentialSenseWorld}
    (value : Bool)
    (initial : DramDifferentialSensePair)
    (required : ℝ)
    (hsupply : world.environment.supply = 5)
    (hinstance :
      world.fabricated = nominalDramDifferentialSenseInstance)
    (hhorizon : 0 ≤ world.environment.horizon)
    (hinitialTrue : initial.1 ∈ Set.Icc (0 : ℝ) 5)
    (hinitialComplement : initial.2 ∈ Set.Icc (0 : ℝ) 5)
    (hinitialOrder :
      if value then initial.2 < initial.1
      else initial.1 < initial.2)
    (hrequiredLower :
      dramDifferentialSenseSignedPairMargin value initial ≤ required)
    (hrequiredUpper : required < 5) :
    Nonempty
      (DramDifferentialSenseResolutionWitness
        world value initial required) := by
  have hdeliveredPositive :
      0 <
        dramDifferentialSenseSignedPairMargin value initial := by
    cases hvalue : value
    · simp only [hvalue, Bool.false_eq_true, if_false] at hinitialOrder
      simp only [dramDifferentialSenseSignedPairMargin,
        hvalue, Bool.false_eq_true, if_false]
      linarith
    · simp only [hvalue, if_true] at hinitialOrder
      simp only [dramDifferentialSenseSignedPairMargin,
        hvalue, if_true]
      linarith
  obtain ⟨trajectory, hinitial, hsolution, hinvariant,
      hmonotone⟩ :=
    dramDifferentialSenseNominalClampedPairRate_realizable_signed_monotone
      value initial hhorizon hinitialTrue hinitialComplement
        hinitialOrder
  obtain ⟨minimumRate, hminimumRate, hdeadline0, hresolves⟩ :=
    dramDifferentialSenseSignedPairMargin_resolution_certificate
      hhorizon hinitial hsolution hinvariant hmonotone
      hdeliveredPositive (le_refl _)
      hrequiredLower hrequiredUpper
  have hresidual :
      ∀ time ∈ Set.Icc (0 : ℝ) world.environment.horizon,
        dramDifferentialSenseDAE.residual world time
          (dramDifferentialSensePairState (trajectory time))
          (dramDifferentialSensePairState
            (dramDifferentialSenseNominalClampedPairRate
              (trajectory time))) := by
    intro time htime
    have hdomain := hinvariant time htime
    exact
      dramDifferentialSenseNominalClampedPairRate_residual
        hsupply hinstance
        ⟨hdomain.1.1, hdomain.1.2,
          hdomain.2.1, hdomain.2.2⟩
  exact
    ⟨⟨trajectory, hinitial, hsolution, hinvariant, hmonotone,
      hresidual, minimumRate, hminimumRate, hdeadline0,
      hresolves⟩⟩

end LeanModels.Spice
