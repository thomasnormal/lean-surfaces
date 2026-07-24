import LeanModels.Spice.Cmos
import LeanModels.Spice.DeviceLevels
import LeanModels.Spice.Mos1Circuit

/-!
# MOS Level 1 compact-model specification

The scalar current below is the long-channel square-law MOS1 channel model
used by the committed ngspice decks. `vgs` and `vds` are polarity-normalized:
for PMOS they mean `Vsg` and `Vsd`. The model currently covers the explicit
deck profile `LEVEL=1`, zero body effect, and no junction-current contribution
to the DC channel equation.
-/

namespace LeanModels.Spice

/-- Real-valued parameters consumed by the channel equation. These are
obtained from the exact validated `Mos1Model`, not from named parameters. -/
structure Mos1Params where
  polarity : MosPolarity
  threshold : ℝ
  beta : ℝ
  lambda : ℝ

noncomputable def Mos1Model.params (model : Mos1Model) : Mos1Params :=
  { polarity := model.polarity
    threshold := (model.threshold : ℝ)
    beta := (model.transconductance : ℝ)
    lambda := (model.channelLengthModulation : ℝ) }

/-- Forward channel-current magnitude for normalized terminal voltages.

The three branches are cutoff, triode, and saturation. -/
noncomputable def mos1ForwardCurrent
    (params : Mos1Params) (vgs vds : ℝ) : ℝ :=
  if vgs ≤ params.threshold then 0
  else if vds ≤ vgs - params.threshold then
    params.beta *
      ((vgs - params.threshold) * vds - vds ^ 2 / 2) *
      (1 + params.lambda * vds)
  else
    params.beta / 2 * (vgs - params.threshold) ^ 2 *
      (1 + params.lambda * vds)

/-- A compact-model terminal-current observation. -/
def Mos1ChannelSpec (params : Mos1Params)
    (vgs vds drainCurrent : ℝ) : Prop :=
  0 ≤ vds ∧ drainCurrent = mos1ForwardCurrent params vgs vds

/-- Real-valued DC state for a typed MOS1 circuit. Source current is positive
from the voltage source's positive terminal to its negative terminal. -/
structure Mos1CircuitState where
  voltage : NodeId → ℝ
  sourceCurrent : SourceId → ℝ

/-- Drain-to-source current using the source orientation written in the deck.
PMOS channel current has the opposite conventional sign. -/
noncomputable def mos1DrainCurrent
    (state : Mos1CircuitState) (transistor : Mos1Transistor) : ℝ :=
  let params := transistor.model.params
  match params.polarity with
  | .nmos =>
      mos1ForwardCurrent params
        (state.voltage transistor.gate - state.voltage transistor.source)
        (state.voltage transistor.drain - state.voltage transistor.source)
  | .pmos =>
      -mos1ForwardCurrent params
        (state.voltage transistor.source - state.voltage transistor.gate)
        (state.voltage transistor.source - state.voltage transistor.drain)

/-- Current leaving one node through one typed device. MOS gate and bulk
currents are zero in this restricted DC channel model. -/
noncomputable def mos1DeviceCurrentLeaving
    (state : Mos1CircuitState) (target : NodeId) : Mos1Device → ℝ
  | .voltageSource source =>
      if target = source.positive then state.sourceCurrent source.id
      else if target = source.negative then -state.sourceCurrent source.id
      else 0
  | .transistor transistor =>
      if target = transistor.drain then mos1DrainCurrent state transistor
      else if target = transistor.source then -mos1DrainCurrent state transistor
      else 0

/-- Total current leaving a named node. -/
noncomputable def mos1Kcl (circuit : Mos1Circuit)
    (state : Mos1CircuitState) (target : NodeId) : ℝ :=
  circuit.devices.toList.foldl
    (fun total device => total + mos1DeviceCurrentLeaving state target device) 0

/-- Nodes mentioned by one typed device. Duplicates are harmless in the
universal KCL condition. -/
abbrev mos1DeviceNodes := Mos1Device.nodes

abbrev mos1Nodes := Mos1Circuit.nodes

/-- Constitutive and operating-orientation requirement for one typed device. -/
noncomputable def Mos1DeviceLaw
    (state : Mos1CircuitState) : Mos1Device → Prop
  | .voltageSource source =>
      state.voltage source.positive - state.voltage source.negative =
        (source.voltage : ℝ)
  | .transistor transistor =>
      match transistor.model.polarity with
      | .nmos =>
          0 ≤ state.voltage transistor.drain - state.voltage transistor.source
      | .pmos =>
          0 ≤ state.voltage transistor.source - state.voltage transistor.drain

/-- The ngspice Level-1 DC semantics used by the proofs:

* hierarchy and model references have already been validated;
* every source and channel satisfies its constitutive equation;
* ground is zero;
* KCL holds at every non-ground terminal node.

Junction currents, body effect, capacitance, and geometry-dependent corrections
are deliberately outside this named profile. -/
noncomputable def Mos1Satisfies
    (circuit : Mos1Circuit) (state : Mos1CircuitState) : Prop :=
  state.voltage ground = 0 ∧
  (∀ device ∈ circuit.devices.toList, Mos1DeviceLaw state device) ∧
  ∀ target ∈ mos1Nodes circuit, target ≠ ground →
    mos1Kcl circuit state target = 0

/-- An operating envelope for static CMOS proofs. This is a named theorem
precondition, not an axiom: all observed nodes must remain between the supply
rails. -/
def Mos1WithinSupply
    (circuit : Mos1Circuit) (state : Mos1CircuitState) : Prop :=
  ∀ target ∈ mos1Nodes circuit,
    0 ≤ state.voltage target ∧ state.voltage target ≤ 5

/-- Extract KCL at a circuit-checked non-ground node. -/
theorem Mos1Satisfies.kclAt
    {circuit : Mos1Circuit} {state : Mos1CircuitState}
    (hsatisfies : Mos1Satisfies circuit state)
    (target : circuit.Node) (hnonground : target.1 ≠ ground) :
    mos1Kcl circuit state target.1 = 0 := by
  exact hsatisfies.2.2 target.1 target.2 hnonground

/-- Extract the supply bounds at a circuit-checked node. -/
theorem Mos1WithinSupply.boundsAt
    {circuit : Mos1Circuit} {state : Mos1CircuitState}
    (hbounded : Mos1WithinSupply circuit state)
    (target : circuit.Node) :
    0 ≤ state.voltage target.1 ∧ state.voltage target.1 ≤ 5 := by
  exact hbounded target.1 target.2

/-- Exact voltage associated with a Boolean input or output. -/
def logicVoltage : Bool → ℝ
  | false => 0
  | true => 5

/-- Ideal external voltage drivers for a two-input MOS1 block. -/
def Mos1DrivesTwo (state : Mos1CircuitState)
    (leftNode rightNode : NodeId) (left right : Bool) : Prop :=
  state.voltage ground = 0 ∧
  state.voltage supply = 5 ∧
  state.voltage leftNode = logicVoltage left ∧
  state.voltage rightNode = logicVoltage right

/-- Soundness contract for an extracted two-input block under the MOS1
equations and the explicitly named static-CMOS supply envelope. -/
noncomputable def Mos1BinaryGateContract (circuit : Mos1Circuit)
    (leftNode rightNode outputNode : NodeId)
    (operation : Bool → Bool → Bool) : Prop :=
  ∀ left right state,
    Mos1Satisfies circuit state →
    Mos1WithinSupply circuit state →
    Mos1DrivesTwo state leftNode rightNode left right →
    state.voltage outputNode = logicVoltage (operation left right)

/-- Soundness contract for a MOS1 half-adder. -/
noncomputable def Mos1HalfAdderContract (circuit : Mos1Circuit)
    (leftNode rightNode sumNode carryNode : NodeId) : Prop :=
  ∀ left right state,
    Mos1Satisfies circuit state →
    Mos1WithinSupply circuit state →
    Mos1DrivesTwo state leftNode rightNode left right →
    state.voltage sumNode = logicVoltage (Bool.xor left right) ∧
      state.voltage carryNode = logicVoltage (Bool.and left right)

/-- One rail-valued observation of a physical MOS1 half-adder instance. -/
noncomputable def Mos1HalfAdderObservation (circuit : Mos1Circuit)
    (leftNode rightNode sumNode carryNode : NodeId)
    (left right sum carry : Bool) : Prop :=
  ∃ state,
    Mos1Satisfies circuit state ∧
    Mos1WithinSupply circuit state ∧
    Mos1DrivesTwo state leftNode rightNode left right ∧
    state.voltage sumNode = logicVoltage sum ∧
    state.voltage carryNode = logicVoltage carry

theorem logicVoltage_injective : Function.Injective logicVoltage := by
  intro left right h
  rcases left with _ | _ <;> rcases right with _ | _ <;>
    simp [logicVoltage] at h ⊢

/-- A proved physical half-adder contract refines each observable instance to
the implementation-independent Boolean half-adder behavior. -/
theorem Mos1HalfAdderContract.observation_sound
    {circuit : Mos1Circuit} {leftNode rightNode sumNode carryNode : NodeId}
    (hcontract :
      Mos1HalfAdderContract circuit leftNode rightNode sumNode carryNode)
    {left right sum carry : Bool}
    (hobservation :
      Mos1HalfAdderObservation circuit leftNode rightNode sumNode carryNode
        left right sum carry) :
    HalfAdderBehavior left right sum carry := by
  rcases hobservation with
    ⟨state, hsatisfies, hbounded, hdrives, hsum, hcarry⟩
  have houtputs :=
    hcontract left right state hsatisfies hbounded hdrives
  constructor
  · apply logicVoltage_injective
    exact hsum.symm.trans houtputs.1
  · apply logicVoltage_injective
    exact hcarry.symm.trans houtputs.2

/-- In the explicit deck profile (`VTO=1`, `LAMBDA=0`, positive beta), a
strongly-on forward channel carrying zero current has zero drain-source
voltage. This is the local fact later used to derive switch behavior. -/
theorem mos1_on_zero_current_iff
    (polarity : MosPolarity) (beta vds : ℝ)
    (hbeta : 0 < beta) (hvds0 : 0 ≤ vds) (hvds5 : vds ≤ 5) :
    mos1ForwardCurrent
        { polarity, threshold := 1, beta, lambda := 0 } 5 vds = 0 ↔
      vds = 0 := by
  unfold mos1ForwardCurrent
  simp only [show ¬(5 : ℝ) ≤ 1 by norm_num, if_false]
  by_cases hregion : vds ≤ 5 - 1
  · simp [hregion]
    constructor
    · intro hzero
      have : beta * (4 * vds - vds ^ 2 / 2) = 0 := by
        norm_num at hzero ⊢
        exact hzero
      rcases mul_eq_zero.mp this with hbeta0 | hshape
      · exact False.elim (ne_of_gt hbeta hbeta0)
      · nlinarith
    · rintro rfl
      norm_num
  · simp [hregion]
    constructor
    · intro hzero
      norm_num at hzero
      nlinarith
    · intro hvds
      subst vds
      norm_num at hregion

/-- With positive transconductance, zero channel-length modulation, and a
forward-oriented channel, the MOS1 current magnitude is nonnegative. -/
theorem mos1ForwardCurrent_nonneg
    (polarity : MosPolarity) (threshold beta vgs vds : ℝ)
    (hbeta : 0 ≤ beta) (hvds : 0 ≤ vds) :
    0 ≤ mos1ForwardCurrent
      { polarity, threshold, beta, lambda := 0 } vgs vds := by
  unfold mos1ForwardCurrent
  split
  · norm_num
  next hon =>
    split
    next htriode =>
      have hoverdrive : 0 < vgs - threshold := by linarith
      have hshape :
          0 ≤ (vgs - threshold) * vds - vds ^ 2 / 2 := by
        nlinarith [mul_nonneg hvds
          (show 0 ≤ vgs - threshold - vds / 2 by linarith)]
      positivity
    next hsaturation =>
      positivity

/-- A strongly-on, forward-oriented MOS1 channel with positive `KP` and
`LAMBDA=0` carries zero current exactly when its terminal voltage drop is
zero. -/
theorem mos1ForwardCurrent_eq_zero_iff
    (polarity : MosPolarity) (threshold beta vgs vds : ℝ)
    (hbeta : 0 < beta) (hon : threshold < vgs) (hvds : 0 ≤ vds) :
    mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 } vgs vds = 0 ↔
      vds = 0 := by
  unfold mos1ForwardCurrent
  simp only [if_neg (not_le.mpr hon)]
  split
  next htriode =>
    constructor
    · intro hzero
      have hfactor :
          beta * ((vgs - threshold) * vds - vds ^ 2 / 2) = 0 := by
        norm_num at hzero ⊢
        exact hzero
      rcases mul_eq_zero.mp hfactor with hbeta0 | hshape
      · exact False.elim (ne_of_gt hbeta hbeta0)
      · nlinarith
    · rintro rfl
      norm_num
  next hsaturation =>
    constructor
    · intro hzero
      norm_num at hzero
      rcases hzero with hbeta0 | hoverdrive0 <;> linarith
    · rintro rfl
      exact False.elim (hsaturation (by linarith))

end LeanModels.Spice
