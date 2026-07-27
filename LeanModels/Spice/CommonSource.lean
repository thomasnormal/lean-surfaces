import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
import LeanModels.Circuit
import LeanModels.Spice.Mos1
import LeanModels.Spice.LoadedInverter

/-!
# Resistor-loaded NMOS common-source amplifier stage

This is a FOCUSED slice in the loaded-inverter style, not generic
compilation: one NMOS transistor in the restricted MOS1 profile
(`LEVEL=1`, `LAMBDA=0`, `IS=0`, positive `VTO`/`KP`) with its source and
bulk grounded, a drain resistor to a supply port, and the gate driven by
an input port. Supply and input drivers belong to the run environment.

The DC behavior relation `CommonSourceDC` contains ONLY physics: the MOS1
channel law, the NMOS channel-orientation admissibility condition, and
KCL at the drain node (which, with two devices at the node, is one
equation equating the resistor current to the channel current).
Operating-point values, the transfer curve, and the saturation window are
all THEOREMS derived from that relation in the Specification layer below
(`commonSource_dc_op`, `commonSource_saturation_safe`, ...), never
conjuncts of it.

The derived operating point is the first nonlinear solve-in-proof in the
lane: the piecewise square law meets the resistor load line, the
triode-branch quadratic is eliminated inside the proof, and on the
saturation branch the drain voltage falls out exactly.
-/

namespace LeanModels.Spice

open LeanModels.Circuit
open Set

/-! ## Instance, environment, and behavior types -/

/-- Typed parameters fixed once for a fabricated common-source stage. -/
structure CommonSourceInstance where
  threshold : ℝ
  beta : ℝ
  drainResistance : ℝ

/-- One DC run of one fabricated stage: the surrounding circuit holds the
supply and input ports at fixed voltages. -/
structure CommonSourceEnvironment where
  supply : ℝ
  input : ℝ

abbrev CommonSourceWorld :=
  RunWorld CommonSourceInstance CommonSourceEnvironment Unit Unit

/-- Observable boundary behavior: the drain (output) voltage. -/
structure CommonSourceBoundary where
  outputVoltage : ℝ

/-! ## Deck adapter -/

/-- Exact data recovered from a typed two-device common-source deck. -/
structure CommonSourceNominal where
  inputNode : LeanModels.Circuit.NodeId
  outputNode : LeanModels.Circuit.NodeId
  supplyNode : LeanModels.Circuit.NodeId
  threshold : Rat
  beta : Rat
  drainResistance : Rat
deriving Repr, BEq, Inhabited

/-- Validate the complete NMOS/drain-resistor topology before exposing
parameters to the DC semantics. The resistor is symmetric, so either
written terminal order is accepted; its non-drain terminal names the
supply port. -/
def ElaboratedCircuit.toCommonSourceNominal
    (circuit : ElaboratedCircuit) :
    Except String CommonSourceNominal := do
  if circuit.devices.size != 2 then
    throw s!"common-source stage requires exactly two devices, found {circuit.devices.size}"
  let mosfets := circuit.devices.toList.filterMap fun
    | .mosfet _ drain gate source bulk model =>
        some (drain, gate, source, bulk, model)
    | _ => none
  let resistors := circuit.devices.toList.filterMap fun
    | .resistor _ positive negative value =>
        some (positive, negative, value)
    | _ => none
  let (drain, gate, source, bulk, modelId) ← match mosfets with
    | [mosfet] => pure mosfet
    | _ => throw "common-source stage requires exactly one MOSFET"
  let (rPositive, rNegative, drainResistance) ← match resistors with
    | [resistor] => pure resistor
    | _ => throw "common-source stage requires exactly one drain resistor"
  let model ← match circuit.models[modelId.index]? with
    | some (.mos1 model) => pure model
    | _ => throw "MOSFET model is missing or unsupported"
  match model.polarity with
  | .pmos => throw "common-source stage requires an NMOS device"
  | .nmos => pure ()
  unless model.channelLengthModulation == 0 &&
      model.junctionSaturation == 0 do
    throw "common-source stage requires the named LAMBDA=0, IS=0 MOS1 profile"
  -- Positivity of a normalized `Rat` is positivity of its numerator; the
  -- integer comparison keeps the whole adapter kernel-reducible (`rfl`).
  if model.threshold.num ≤ 0 || model.transconductance.num ≤ 0 then
    throw "common-source stage requires positive VTO and KP"
  if drainResistance.num ≤ 0 then
    throw "common-source stage requires a positive drain resistance"
  unless source == circuit.ground && bulk == circuit.ground do
    throw "common-source stage requires a grounded source and bulk"
  let supplyNode ←
    if rPositive == drain then pure rNegative
    else if rNegative == drain then pure rPositive
    else throw "the drain resistor must connect to the MOSFET drain"
  unless supplyNode != circuit.ground && supplyNode != drain &&
      supplyNode != gate && gate != drain && gate != circuit.ground do
    throw "common-source ports in, out, vdd, and ground must be distinct"
  pure
    { inputNode := gate
      outputNode := drain
      supplyNode
      threshold := model.threshold
      beta := model.transconductance
      drainResistance }

noncomputable def CommonSourceNominal.instance
    (nominal : CommonSourceNominal) : CommonSourceInstance :=
  { threshold := nominal.threshold
    beta := nominal.beta
    drainResistance := nominal.drainResistance }

noncomputable def CommonSourceNominal.world
    (nominal : CommonSourceNominal) (supply input : ℝ) :
    CommonSourceWorld :=
  deterministicWorld nominal.instance { supply, input }

/-! ## DC behavior relation (physics only)

Conjuncts: NMOS channel orientation (`Mos1DeviceLaw` for a grounded
source), and KCL at the drain node with the resistor Ohm law and the MOS1
channel law substituted for the two branch currents. With the source at
ground, `vgs = input` and `vds = output`. -/

def CommonSourceDC (fabricated : CommonSourceInstance)
    (supply input output : ℝ) : Prop :=
  0 ≤ output ∧
  (supply - output) / fabricated.drainResistance =
    mos1ForwardCurrent
      { polarity := .nmos, threshold := fabricated.threshold,
        beta := fabricated.beta, lambda := 0 }
      input output

/-- The stage's DC denotation as a lane behavior relation. -/
def CommonSourceBehavior :
    Behavior CommonSourceWorld CommonSourceBoundary Unit :=
  fun world boundary _internal =>
    CommonSourceDC world.fabricated world.environment.supply
      world.environment.input boundary.outputVoltage

/-- Physical and proof-domain conditions for a DC run. -/
def CommonSourceAdmissible (world : CommonSourceWorld) : Prop :=
  0 < world.fabricated.beta ∧
  0 < world.fabricated.threshold ∧
  0 < world.fabricated.drainResistance ∧
  0 ≤ world.environment.supply

/-- The saturation window: the device conducts and the load line still
meets the square law at or above the overdrive. The inequality is exactly
"the saturation-branch drain voltage is at least the overdrive",
pre-stated on the environment so it can gate theorems. -/
def CommonSourceSaturationRun (world : CommonSourceWorld) : Prop :=
  CommonSourceAdmissible world ∧
  world.fabricated.threshold < world.environment.input ∧
  world.fabricated.beta * world.fabricated.drainResistance / 2 *
      (world.environment.input - world.fabricated.threshold) ^ 2 +
    (world.environment.input - world.fabricated.threshold) ≤
    world.environment.supply

/-! ## Region analysis -/

/-- With `LAMBDA = 0` the MOS1 forward current is monotone in the
drain-source drop: constant in cutoff, increasing through triode, and
constant in saturation. This is the device half of the uniqueness
argument (the resistor load line is the strictly decreasing half). -/
theorem mos1ForwardCurrent_mono_drop
    (polarity : LeanModels.Circuit.MosPolarity) (threshold beta vgs : ℝ)
    (hbeta : 0 ≤ beta) {vds₁ vds₂ : ℝ} (hle : vds₁ ≤ vds₂) :
    mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 } vgs vds₁ ≤
      mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 } vgs vds₂ := by
  unfold mos1ForwardCurrent
  by_cases hcutoff : vgs ≤ threshold
  · simp [hcutoff]
  · simp only [hcutoff, if_false]
    have hon : threshold < vgs := lt_of_not_ge hcutoff
    by_cases h₂ : vds₂ ≤ vgs - threshold
    · have h₁ : vds₁ ≤ vgs - threshold := le_trans hle h₂
      simp only [h₁, h₂, if_true]
      have hproduct :
          0 ≤ beta * ((vds₂ - vds₁) *
            ((vgs - threshold) - (vds₁ + vds₂) / 2)) :=
        mul_nonneg hbeta
          (mul_nonneg (by linarith) (by linarith))
      nlinarith [hproduct]
    · by_cases h₁ : vds₁ ≤ vgs - threshold
      · simp only [h₁, if_true, h₂, if_false]
        nlinarith [mul_nonneg hbeta (sq_nonneg (vgs - threshold - vds₁))]
      · simp only [h₁, h₂, if_false]
        nlinarith []

/-- Cutoff clipping: at or below threshold the channel carries no current,
so the resistor pins the drain to the supply rail. -/
theorem commonSource_dc_cutoff
    {fabricated : CommonSourceInstance} {supply input output : ℝ}
    (hrd : fabricated.drainResistance ≠ 0)
    (hcutoff : input ≤ fabricated.threshold)
    (hdc : CommonSourceDC fabricated supply input output) :
    output = supply := by
  obtain ⟨_houtput0, hkcl⟩ := hdc
  unfold mos1ForwardCurrent at hkcl
  rw [if_pos hcutoff, div_eq_iff hrd, zero_mul] at hkcl
  linarith

/-- The derived operating point. Inside the saturation window every DC
state sits at exactly the saturation-branch load-line voltage. The proof
performs the nonlinear solve: on the triode branch the KCL quadratic
`β(V_ov·v − v²/2) = (V_DD − v)/R_D` is squeezed against the window
inequality until `v = V_ov` (the branch boundary, where it agrees with
the saturation value); on the saturation branch the drain voltage is
solved directly. Nothing on the right-hand side is asserted anywhere in
the behavior relation. -/
theorem commonSource_dc_op
    {fabricated : CommonSourceInstance} {supply input output : ℝ}
    (hbeta : 0 < fabricated.beta)
    (hrd : 0 < fabricated.drainResistance)
    (hon : fabricated.threshold < input)
    (hwindow :
      fabricated.beta * fabricated.drainResistance / 2 *
          (input - fabricated.threshold) ^ 2 +
        (input - fabricated.threshold) ≤ supply)
    (hdc : CommonSourceDC fabricated supply input output) :
    output =
      supply -
        fabricated.beta * fabricated.drainResistance / 2 *
          (input - fabricated.threshold) ^ 2 := by
  obtain ⟨houtput0, hkcl⟩ := hdc
  unfold mos1ForwardCurrent at hkcl
  rw [if_neg (not_le.mpr hon)] at hkcl
  by_cases htriode : output ≤ input - fabricated.threshold
  · rw [if_pos htriode, div_eq_iff (ne_of_gt hrd)] at hkcl
    have hboundary : input - fabricated.threshold ≤ output := by
      nlinarith [hkcl, hwindow,
        mul_nonneg (mul_nonneg hbeta.le hrd.le)
          (sq_nonneg (input - fabricated.threshold - output))]
    have hedge : output = input - fabricated.threshold :=
      le_antisymm htriode hboundary
    rw [hedge] at hkcl ⊢
    nlinarith [hkcl]
  · rw [if_neg htriode, div_eq_iff (ne_of_gt hrd)] at hkcl
    linear_combination -hkcl

/-- Saturation-region membership is derived, not assumed: inside the
window the drain voltage stays at or above the overdrive. This is the
validity domain for the small-signal gain work. -/
theorem commonSource_dc_saturation
    {fabricated : CommonSourceInstance} {supply input output : ℝ}
    (hbeta : 0 < fabricated.beta)
    (hrd : 0 < fabricated.drainResistance)
    (hon : fabricated.threshold < input)
    (hwindow :
      fabricated.beta * fabricated.drainResistance / 2 *
          (input - fabricated.threshold) ^ 2 +
        (input - fabricated.threshold) ≤ supply)
    (hdc : CommonSourceDC fabricated supply input output) :
    input - fabricated.threshold ≤ output := by
  have hop := commonSource_dc_op hbeta hrd hon hwindow hdc
  linarith [hop, hwindow]

/-! ## Triode / clipping region

Beyond the saturation window the load line meets the square law inside
the triode branch and the output is pinned near the low rail. Branch
membership, the exact clipped voltage, and an honest rail-pinning bound
are all derived from the same physics-only relation. -/

/-- Deep-triode branch membership is derived, not assumed: when the
window inequality fails strictly, no DC state can sit on the saturation
branch (the saturation drain voltage would certify the window), so the
drain drops strictly below the overdrive. -/
theorem commonSource_dc_triode_membership
    {fabricated : CommonSourceInstance} {supply input output : ℝ}
    (_hbeta : 0 < fabricated.beta)
    (hrd : 0 < fabricated.drainResistance)
    (hon : fabricated.threshold < input)
    (hdeep : supply <
      fabricated.beta * fabricated.drainResistance / 2 *
          (input - fabricated.threshold) ^ 2 +
        (input - fabricated.threshold))
    (hdc : CommonSourceDC fabricated supply input output) :
    output < input - fabricated.threshold := by
  obtain ⟨_houtput0, hkcl⟩ := hdc
  unfold mos1ForwardCurrent at hkcl
  rw [if_neg (not_le.mpr hon)] at hkcl
  by_contra hge
  rw [not_lt] at hge
  by_cases htriode : output ≤ input - fabricated.threshold
  · have hedge : output = input - fabricated.threshold :=
      le_antisymm htriode hge
    rw [if_pos htriode, div_eq_iff (ne_of_gt hrd)] at hkcl
    rw [hedge] at hkcl
    nlinarith [hkcl, hdeep]
  · rw [if_neg htriode, div_eq_iff (ne_of_gt hrd)] at hkcl
    rw [not_le] at htriode
    nlinarith [hkcl, hdeep, htriode]

/-- The exact clipped output voltage. In deep triode the KCL quadratic
`β·R_D/2·v² − (β·R_D·V_ov + 1)·v + V_DD = 0` completes to the square
`(G − β·R_D·v)² = G² − 2·β·R_D·V_DD` with `G = β·R_D·V_ov + 1`, and
branch membership selects the smaller root. The discriminant is
nonnegative because it IS that square — solvability is inherited from the
DC state, never assumed. -/
theorem commonSource_dc_triode
    {fabricated : CommonSourceInstance} {supply input output : ℝ}
    (hbeta : 0 < fabricated.beta)
    (hrd : 0 < fabricated.drainResistance)
    (hon : fabricated.threshold < input)
    (hdeep : supply <
      fabricated.beta * fabricated.drainResistance / 2 *
          (input - fabricated.threshold) ^ 2 +
        (input - fabricated.threshold))
    (hdc : CommonSourceDC fabricated supply input output) :
    output =
      (fabricated.beta * fabricated.drainResistance *
            (input - fabricated.threshold) + 1 -
          Real.sqrt
            ((fabricated.beta * fabricated.drainResistance *
                  (input - fabricated.threshold) + 1) ^ 2 -
              2 * fabricated.beta * fabricated.drainResistance * supply)) /
        (fabricated.beta * fabricated.drainResistance) := by
  have hmem := commonSource_dc_triode_membership hbeta hrd hon hdeep hdc
  obtain ⟨_houtput0, hkcl⟩ := hdc
  unfold mos1ForwardCurrent at hkcl
  rw [if_neg (not_le.mpr hon), if_pos hmem.le,
    div_eq_iff (ne_of_gt hrd)] at hkcl
  have hbrd : 0 < fabricated.beta * fabricated.drainResistance :=
    mul_pos hbeta hrd
  have hsq :
      (fabricated.beta * fabricated.drainResistance *
            (input - fabricated.threshold) + 1) ^ 2 -
          2 * fabricated.beta * fabricated.drainResistance * supply =
        (fabricated.beta * fabricated.drainResistance *
              (input - fabricated.threshold) + 1 -
            fabricated.beta * fabricated.drainResistance * output) ^ 2 := by
    linear_combination
      (-2 * fabricated.beta * fabricated.drainResistance) * hkcl
  have hpos :
      0 ≤ fabricated.beta * fabricated.drainResistance *
            (input - fabricated.threshold) + 1 -
          fabricated.beta * fabricated.drainResistance * output := by
    nlinarith [mul_pos hbrd (sub_pos.mpr hmem)]
  rw [hsq, Real.sqrt_sq hpos, sub_sub_cancel,
    mul_div_cancel_left₀ _ (ne_of_gt hbrd)]

/-- Honest rail-pinning bound for the clipped region, division-free: the
clipped output satisfies `v·(2 + β·R_D·V_ov) ≤ 2·V_DD`, so it collapses
toward the low rail as the overdrive grows. -/
theorem commonSource_dc_triode_bound
    {fabricated : CommonSourceInstance} {supply input output : ℝ}
    (hbeta : 0 < fabricated.beta)
    (hrd : 0 < fabricated.drainResistance)
    (hon : fabricated.threshold < input)
    (hdeep : supply <
      fabricated.beta * fabricated.drainResistance / 2 *
          (input - fabricated.threshold) ^ 2 +
        (input - fabricated.threshold))
    (hdc : CommonSourceDC fabricated supply input output) :
    output *
        (2 + fabricated.beta * fabricated.drainResistance *
          (input - fabricated.threshold)) ≤
      2 * supply := by
  have hmem := commonSource_dc_triode_membership hbeta hrd hon hdeep hdc
  obtain ⟨houtput0, hkcl⟩ := hdc
  unfold mos1ForwardCurrent at hkcl
  rw [if_neg (not_le.mpr hon), if_pos hmem.le,
    div_eq_iff (ne_of_gt hrd)] at hkcl
  nlinarith [hkcl,
    mul_nonneg (mul_nonneg (mul_pos hbeta hrd).le houtput0)
      (sub_pos.mpr hmem).le]

/-- Uniqueness of the DC operating point for every input: the resistor
load line is strictly decreasing in the drain voltage while the channel
current is monotone increasing, so two admissible solutions coincide. -/
theorem commonSource_dc_determinate
    {fabricated : CommonSourceInstance} {supply input output₁ output₂ : ℝ}
    (hbeta : 0 ≤ fabricated.beta)
    (hrd : 0 < fabricated.drainResistance)
    (h₁ : CommonSourceDC fabricated supply input output₁)
    (h₂ : CommonSourceDC fabricated supply input output₂) :
    output₁ = output₂ := by
  have key : ∀ low high : ℝ,
      CommonSourceDC fabricated supply input low →
      CommonSourceDC fabricated supply input high →
      low < high → False := by
    intro low high hlow hhigh hlt
    obtain ⟨_hlow0, hlowKcl⟩ := hlow
    obtain ⟨_hhigh0, hhighKcl⟩ := hhigh
    have hmono :=
      mos1ForwardCurrent_mono_drop .nmos fabricated.threshold
        fabricated.beta input hbeta hlt.le
    rw [← hlowKcl, ← hhighKcl] at hmono
    have hscaled :=
      mul_le_mul_of_nonneg_right hmono hrd.le
    rw [div_mul_cancel₀ _ (ne_of_gt hrd),
      div_mul_cancel₀ _ (ne_of_gt hrd)] at hscaled
    linarith
  rcases lt_trichotomy output₁ output₂ with hlt | heq | hgt
  · exact (key output₁ output₂ h₁ h₂ hlt).elim
  · exact heq
  · exact (key output₂ output₁ h₂ h₁ hgt).elim

/-! ## Existence -/

/-- The nonlinear DC equation has an operating point for every input in
every admissible world, by the intermediate value theorem applied to the
continuous branch-glued channel current (the piecewise MOS1 branches
agree at their boundaries when `LAMBDA = 0`, via the continuous
`mos1EnvelopeCurrent` extension). -/
theorem commonSource_dc_exists
    (fabricated : CommonSourceInstance) (input : ℝ) {supply : ℝ}
    (hsupply : 0 ≤ supply)
    (hbeta : 0 ≤ fabricated.beta)
    (hrd : 0 < fabricated.drainResistance) :
    ∃ output, CommonSourceDC fabricated supply input output := by
  let residual : ℝ → ℝ := fun output =>
    mos1EnvelopeCurrent fabricated.beta fabricated.threshold
        input output -
      (supply - output) / fabricated.drainResistance
  have hcontinuous : Continuous residual := by
    apply Continuous.sub
    · exact mos1EnvelopeCurrent_continuous _ _ _
    · exact (continuous_const.sub continuous_id).div_const _
  have hzeroDrop :
      mos1EnvelopeCurrent fabricated.beta fabricated.threshold
        input 0 = 0 := by
    simp [mos1EnvelopeCurrent, railCurrent, clampedDrop]
  have hleft : residual 0 ≤ 0 := by
    have hpull : (0 : ℝ) ≤ supply / fabricated.drainResistance :=
      div_nonneg hsupply hrd.le
    simp only [residual, hzeroDrop, sub_zero]
    linarith
  have hright : 0 ≤ residual supply := by
    have hcurrent :
        0 ≤ mos1EnvelopeCurrent fabricated.beta fabricated.threshold
          input supply :=
      railCurrent_nonneg hbeta (le_max_left _ _)
    simp only [residual, sub_self, zero_div]
    linarith
  obtain ⟨output, hbounds, hresidual⟩ :=
    intermediate_value_Icc hsupply hcontinuous.continuousOn
      ⟨hleft, hright⟩
  refine ⟨output, hbounds.1, ?_⟩
  have hexact :
      mos1EnvelopeCurrent fabricated.beta fabricated.threshold
          input output =
        mos1ForwardCurrent
          { polarity := .nmos, threshold := fabricated.threshold,
            beta := fabricated.beta, lambda := 0 }
          input output :=
    mos1EnvelopeCurrent_eq_mos1 (polarity := .nmos) hbeta hbounds.1
  have hzero : residual output = 0 := hresidual
  simp only [residual, hexact] at hzero
  linarith

/-! ## Transfer curve and small-signal gain

`commonSourceTransfer` is Specification-layer bookkeeping: a name for the
closed form that `commonSource_dc_op` DERIVES from the physics relation.
It never appears in `CommonSourceDC`; the theorems below re-derive every
connection through the behavior relation. -/

/-- The derived saturation-window transfer curve
`v ↦ V_DD − β·R_D/2·(v − V_TO)²`. -/
noncomputable def commonSourceTransfer
    (fabricated : CommonSourceInstance) (supply : ℝ) : ℝ → ℝ :=
  fun input =>
    supply - fabricated.beta * fabricated.drainResistance / 2 *
      (input - fabricated.threshold) ^ 2

/-- Window monotonicity: the saturation-window inequality at a higher
input implies it at every conducting lower input. Lets a single endpoint
check gate a whole interval. -/
theorem commonSource_window_mono
    {fabricated : CommonSourceInstance} {supply v hi : ℝ}
    (hbeta : 0 < fabricated.beta)
    (hrd : 0 < fabricated.drainResistance)
    (hon : fabricated.threshold < v) (hle : v ≤ hi)
    (hwindow :
      fabricated.beta * fabricated.drainResistance / 2 *
          (hi - fabricated.threshold) ^ 2 +
        (hi - fabricated.threshold) ≤ supply) :
    fabricated.beta * fabricated.drainResistance / 2 *
        (v - fabricated.threshold) ^ 2 +
      (v - fabricated.threshold) ≤ supply := by
  nlinarith [mul_nonneg (mul_nonneg hbeta.le hrd.le)
    (mul_nonneg (sub_nonneg.mpr hle)
      (by linarith : (0 : ℝ) ≤ hi + v - 2 * fabricated.threshold))]

/-- Realizability of the transfer curve pointwise: inside the window the
derived closed form IS a DC state of the physics relation (constructed
directly on the correct branch, including the branch-boundary case where
the window inequality is tight). -/
theorem commonSource_dc_transfer_realizable
    {fabricated : CommonSourceInstance} {supply input : ℝ}
    (_hbeta : 0 < fabricated.beta)
    (hrd : 0 < fabricated.drainResistance)
    (hon : fabricated.threshold < input)
    (hwindow :
      fabricated.beta * fabricated.drainResistance / 2 *
          (input - fabricated.threshold) ^ 2 +
        (input - fabricated.threshold) ≤ supply) :
    CommonSourceDC fabricated supply input
      (commonSourceTransfer fabricated supply input) := by
  have hVov : 0 < input - fabricated.threshold := sub_pos.mpr hon
  refine ⟨by unfold commonSourceTransfer; nlinarith, ?_⟩
  unfold commonSourceTransfer mos1ForwardCurrent
  rw [if_neg (not_le.mpr hon)]
  by_cases hedge :
      supply - fabricated.beta * fabricated.drainResistance / 2 *
          (input - fabricated.threshold) ^ 2 ≤
        input - fabricated.threshold
  · have heq :
        supply - fabricated.beta * fabricated.drainResistance / 2 *
            (input - fabricated.threshold) ^ 2 =
          input - fabricated.threshold :=
      le_antisymm hedge (by nlinarith)
    rw [if_pos hedge, heq, div_eq_iff (ne_of_gt hrd)]
    linear_combination heq
  · rw [if_neg hedge, div_eq_iff (ne_of_gt hrd)]
    ring

/-- The transfer curve's literal mathlib derivative at every input: the
textbook small-signal gain `−g_m·R_D = −β·(V_in − V_TO)·R_D`. -/
theorem commonSourceTransfer_hasDerivAt
    (fabricated : CommonSourceInstance) (supply input : ℝ) :
    HasDerivAt (commonSourceTransfer fabricated supply)
      (-(fabricated.beta * (input - fabricated.threshold) *
        fabricated.drainResistance)) input := by
  have hsq : HasDerivAt
      (fun v : ℝ => (v - fabricated.threshold) ^ 2)
      (2 * (input - fabricated.threshold)) input :=
    (((hasDerivAt_id input).sub_const fabricated.threshold).pow 2).congr_deriv
      (by norm_num)
  exact ((hsq.const_mul
      (fabricated.beta * fabricated.drainResistance / 2)).const_sub
    supply).congr_deriv (by ring)

/-- THE GAIN THEOREM. Any function that solves the physics-only DC
relation on an open window around the bias has a literal mathlib
derivative there, and it equals `−g_m·R_D`: the behavior relation pins
every solution family to the derived transfer curve on a neighborhood, so
differentiability and the gain value transfer over. Nothing about the
solution family beyond the DC relation itself is assumed. -/
theorem commonSource_gain
    {fabricated : CommonSourceInstance} {supply lo hi bias : ℝ}
    (hbeta : 0 < fabricated.beta)
    (hrd : 0 < fabricated.drainResistance)
    (hlo : lo < bias) (hhi : bias < hi)
    (hon : fabricated.threshold ≤ lo)
    (hwindow :
      fabricated.beta * fabricated.drainResistance / 2 *
          (hi - fabricated.threshold) ^ 2 +
        (hi - fabricated.threshold) ≤ supply)
    {vout : ℝ → ℝ}
    (hsol : ∀ v ∈ Set.Ioo lo hi,
      CommonSourceDC fabricated supply v (vout v)) :
    HasDerivAt vout
      (-(fabricated.beta * (bias - fabricated.threshold) *
        fabricated.drainResistance)) bias := by
  apply (commonSourceTransfer_hasDerivAt fabricated supply
    bias).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds hlo hhi] with v hv
  have honv : fabricated.threshold < v := lt_of_le_of_lt hon hv.1
  exact commonSource_dc_op hbeta hrd honv
    (commonSource_window_mono hbeta hrd honv hv.2.le hwindow) (hsol v hv)

/-- Realizability twin for the gain theorem: a solution family satisfying
its hypothesis exists — the derived transfer curve itself. -/
theorem commonSource_gain_realizable
    {fabricated : CommonSourceInstance} {supply lo hi bias : ℝ}
    (hbeta : 0 < fabricated.beta)
    (hrd : 0 < fabricated.drainResistance)
    (_hlo : lo < bias) (_hhi : bias < hi)
    (hon : fabricated.threshold ≤ lo)
    (hwindow :
      fabricated.beta * fabricated.drainResistance / 2 *
          (hi - fabricated.threshold) ^ 2 +
        (hi - fabricated.threshold) ≤ supply) :
    ∃ vout : ℝ → ℝ,
      (∀ v ∈ Set.Ioo lo hi,
        CommonSourceDC fabricated supply v (vout v)) ∧
      HasDerivAt vout
        (-(fabricated.beta * (bias - fabricated.threshold) *
          fabricated.drainResistance)) bias := by
  refine ⟨commonSourceTransfer fabricated supply, fun v hv => ?_,
    commonSourceTransfer_hasDerivAt fabricated supply bias⟩
  have honv : fabricated.threshold < v := lt_of_le_of_lt hon hv.1
  exact commonSource_dc_transfer_realizable hbeta hrd honv
    (commonSource_window_mono hbeta hrd honv hv.2.le hwindow)

/-- Exact second-order linearization identity between any two DC states
in the window: the deviation from the small-signal prediction is EXACTLY
`−β·R_D/2·d²`. For the quadratic device law the "linearity error bound"
is an equality, strictly stronger than any datasheet-style `≤` spec. -/
theorem commonSource_dc_linearization
    {fabricated : CommonSourceInstance} {supply bias d out0 outd : ℝ}
    (hbeta : 0 < fabricated.beta)
    (hrd : 0 < fabricated.drainResistance)
    (hon0 : fabricated.threshold < bias)
    (hond : fabricated.threshold < bias + d)
    (hwin0 :
      fabricated.beta * fabricated.drainResistance / 2 *
          (bias - fabricated.threshold) ^ 2 +
        (bias - fabricated.threshold) ≤ supply)
    (hwind :
      fabricated.beta * fabricated.drainResistance / 2 *
          (bias + d - fabricated.threshold) ^ 2 +
        (bias + d - fabricated.threshold) ≤ supply)
    (h0 : CommonSourceDC fabricated supply bias out0)
    (hd : CommonSourceDC fabricated supply (bias + d) outd) :
    outd - out0 +
        fabricated.beta * (bias - fabricated.threshold) *
          fabricated.drainResistance * d =
      -(fabricated.beta * fabricated.drainResistance / 2) * d ^ 2 := by
  rw [commonSource_dc_op hbeta hrd hon0 hwin0 h0,
    commonSource_dc_op hbeta hrd hond hwind hd]
  ring

/-! ## Tolerance-box robustness (bench-measurement intervals)

Fabricated parts do not hit nominal `V_TO`/`KP`. The corner lemmas below
lift the RobustDivider box pattern to the nonlinear stage: one
worst-corner check gates the saturation window for every part in a
parameter box, and the derived gain of every part is pinned between the
two extreme corners. The box is a hypothesis about the fabricated
instance — nothing here enlarges the behavior relation. -/

/-- One worst-corner check (highest `β`, lowest `V_TO`) dominates the
saturation-window inequality for every part in the box. -/
theorem commonSource_window_box
    {fabricated : CommonSourceInstance}
    {supply hi tLo tHi bLo bHi : ℝ}
    (hvto : fabricated.threshold ∈ Set.Icc tLo tHi)
    (hbeta : fabricated.beta ∈ Set.Icc bLo bHi)
    (hrd : 0 < fabricated.drainResistance)
    (hbLo : 0 ≤ bLo) (hhi : tHi ≤ hi)
    (hcorner :
      bHi * fabricated.drainResistance / 2 * (hi - tLo) ^ 2 +
        (hi - tLo) ≤ supply) :
    fabricated.beta * fabricated.drainResistance / 2 *
        (hi - fabricated.threshold) ^ 2 +
      (hi - fabricated.threshold) ≤ supply := by
  obtain ⟨htLo, htHi⟩ := hvto
  obtain ⟨hbLo', hbHi⟩ := hbeta
  have hbX :
      fabricated.beta * (hi - fabricated.threshold) ^ 2 ≤
        bHi * (hi - tLo) ^ 2 := by
    have hsq : (hi - fabricated.threshold) ^ 2 ≤ (hi - tLo) ^ 2 := by
      nlinarith
    nlinarith [sq_nonneg (hi - fabricated.threshold)]
  have hscaled :=
    mul_le_mul_of_nonneg_left hbX
      (by positivity : (0 : ℝ) ≤ fabricated.drainResistance / 2)
  nlinarith [hscaled]

/-- The derived gain of every part in the box lies between the two
extreme corners: the fastest corner (highest `β`, lowest `V_TO`) and the
slowest corner (lowest `β`, highest `V_TO`). -/
theorem commonSource_gain_box
    {fabricated : CommonSourceInstance} {bias tLo tHi bLo bHi : ℝ}
    (hvto : fabricated.threshold ∈ Set.Icc tLo tHi)
    (hbeta : fabricated.beta ∈ Set.Icc bLo bHi)
    (hrd : 0 ≤ fabricated.drainResistance)
    (hbLo : 0 ≤ bLo) (hbias : tHi ≤ bias) :
    -(fabricated.beta * (bias - fabricated.threshold) *
        fabricated.drainResistance) ∈
      Set.Icc (-(bHi * (bias - tLo) * fabricated.drainResistance))
        (-(bLo * (bias - tHi) * fabricated.drainResistance)) := by
  obtain ⟨htLo, htHi⟩ := hvto
  obtain ⟨hbLo', hbHi⟩ := hbeta
  constructor
  · rw [neg_le_neg_iff]
    refine mul_le_mul_of_nonneg_right ?_ hrd
    have ha :
        fabricated.beta * (bias - fabricated.threshold) ≤
          bHi * (bias - fabricated.threshold) :=
      mul_le_mul_of_nonneg_right hbHi (by linarith)
    have hb : bHi * (bias - fabricated.threshold) ≤ bHi * (bias - tLo) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith
  · rw [neg_le_neg_iff]
    refine mul_le_mul_of_nonneg_right ?_ hrd
    have ha :
        bLo * (bias - tHi) ≤ fabricated.beta * (bias - tHi) :=
      mul_le_mul_of_nonneg_right hbLo' (by linarith)
    have hb :
        fabricated.beta * (bias - tHi) ≤
          fabricated.beta * (bias - fabricated.threshold) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    linarith

/-! ## Behavior-level pairing (design law: every behavior theorem ships
with a realizability twin) -/

theorem commonSource_realizable :
    RealizableUnder CommonSourceBehavior CommonSourceAdmissible := by
  intro world hadmissible
  obtain ⟨output, hdc⟩ :=
    commonSource_dc_exists world.fabricated world.environment.input
      hadmissible.2.2.2 hadmissible.1.le hadmissible.2.2.1
  exact ⟨⟨output⟩, (), hdc⟩

/-- Specification layer: on the saturation window, every DC state has the
device saturated and the drain at the derived load-line voltage. -/
theorem commonSource_saturation_safe :
    SafeUnder CommonSourceBehavior CommonSourceSaturationRun
      (fun world boundary _internal =>
        world.environment.input - world.fabricated.threshold ≤
            boundary.outputVoltage ∧
          boundary.outputVoltage =
            world.environment.supply -
              world.fabricated.beta * world.fabricated.drainResistance / 2 *
                (world.environment.input - world.fabricated.threshold) ^ 2) := by
  intro world boundary _internal hallowed hbehavior
  obtain ⟨hadmissible, hon, hwindow⟩ := hallowed
  exact
    ⟨commonSource_dc_saturation hadmissible.1 hadmissible.2.2.1
        hon hwindow hbehavior,
      commonSource_dc_op hadmissible.1 hadmissible.2.2.1
        hon hwindow hbehavior⟩

theorem commonSource_saturation_realizable :
    RealizableUnder CommonSourceBehavior CommonSourceSaturationRun := by
  intro world hallowed
  exact commonSource_realizable world hallowed.1

/-- The clipping window: the device conducts but the load line has left
the square law's saturation reach, mirroring `CommonSourceSaturationRun`
on the other side of the boundary. -/
def CommonSourceTriodeRun (world : CommonSourceWorld) : Prop :=
  CommonSourceAdmissible world ∧
  world.fabricated.threshold < world.environment.input ∧
  world.environment.supply <
    world.fabricated.beta * world.fabricated.drainResistance / 2 *
        (world.environment.input - world.fabricated.threshold) ^ 2 +
      (world.environment.input - world.fabricated.threshold)

/-- Specification layer for clipping: in the triode window every DC state
has the drain strictly below the overdrive and pinned toward the low rail
by the division-free bound. -/
theorem commonSource_triode_safe :
    SafeUnder CommonSourceBehavior CommonSourceTriodeRun
      (fun world boundary _internal =>
        boundary.outputVoltage <
            world.environment.input - world.fabricated.threshold ∧
          boundary.outputVoltage *
              (2 + world.fabricated.beta * world.fabricated.drainResistance *
                (world.environment.input - world.fabricated.threshold)) ≤
            2 * world.environment.supply) := by
  intro world boundary _internal hallowed hbehavior
  obtain ⟨hadmissible, hon, hdeep⟩ := hallowed
  exact
    ⟨commonSource_dc_triode_membership hadmissible.1 hadmissible.2.2.1
        hon hdeep hbehavior,
      commonSource_dc_triode_bound hadmissible.1 hadmissible.2.2.1
        hon hdeep hbehavior⟩

theorem commonSource_triode_realizable :
    RealizableUnder CommonSourceBehavior CommonSourceTriodeRun := by
  intro world hallowed
  exact commonSource_realizable world hallowed.1

/-- The observed drain voltage is the same in every admitted behavior of
an admissible world. -/
theorem commonSource_determinate :
    DeterminateUnder CommonSourceBehavior CommonSourceAdmissible ℝ
      (fun _world boundary _internal => boundary.outputVoltage) := by
  intro world hadmissible boundary₁ _internal₁ boundary₂ _internal₂
    h₁ h₂
  exact commonSource_dc_determinate hadmissible.1.le
    hadmissible.2.2.1 h₁ h₂

/-! ## Evidence layer -/

/-- Provenance record for the ngspice `.op` differential harness on this
stage. Metadata only; it proves nothing by itself. -/
def commonSourceHarnessEvidence : EvidenceRecord :=
  { artifact := "harness/spice/amp_test.py"
    artifactHash := ""
    version := "ngspice-46"
    issuer := "spice amp harness"
    modality := .finiteValidation
    domainDescription :=
      "cs_amp.cir bias sweep vin ∈ {1/2, 1, 3/2, 2, 9/4, 3} at vdd = 5: ngspice .op against the exact rational operating points derived in Lean"
    confidenceDescription :=
      "floating-point agreement within 1e-6 relative at tightened solver tolerances" }

/-- The MOS1-envelope validity claim for this stage: a physical DC
relation for a fabricated part is covered by `CommonSourceBehavior` on
the saturation window. Accepting it requires an actual proof or an
explicit calibration hypothesis — the evidence record alone cannot
construct `AcceptedValidity`. -/
def commonSourceEnvelopeClaim
    (physical : Behavior CommonSourceWorld CommonSourceBoundary Unit) :
    ValidityClaim CommonSourceWorld CommonSourceBoundary Unit :=
  { physical
    envelope := CommonSourceBehavior
    domain := fun world _boundary _internal =>
      CommonSourceSaturationRun world }

/-- Pair the harness provenance with an explicit acceptance hypothesis.
Bench calibration later replaces the hypothesis; nothing here is assumed
silently. -/
def commonSourceAcceptedValidity
    (physical : Behavior CommonSourceWorld CommonSourceBoundary Unit)
    (haccepted : (commonSourceEnvelopeClaim physical).statement) :
    AcceptedValidity (commonSourceEnvelopeClaim physical) :=
  { evidence := commonSourceHarnessEvidence
    accepted := haccepted }

end LeanModels.Spice

namespace LeanModels.Circuit

/-- Type-namespace wrapper so field notation on the shared parsed circuit
resolves without exposing the SPICE implementation namespace. -/
def ElaboratedCircuit.toCommonSourceNominal
    (circuit : ElaboratedCircuit) :
    Except String LeanModels.Spice.CommonSourceNominal :=
  LeanModels.Spice.ElaboratedCircuit.toCommonSourceNominal circuit

end LeanModels.Circuit
