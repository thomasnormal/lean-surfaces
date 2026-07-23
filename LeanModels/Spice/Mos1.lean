import LeanModels.Spice.Cmos
import LeanModels.Spice.DeviceLevels

/-!
# MOS Level 1 compact-model specification

The scalar current below is the long-channel square-law MOS1 channel model
used by the committed ngspice decks. `vgs` and `vds` are polarity-normalized:
for PMOS they mean `Vsg` and `Vsd`. The model currently covers the explicit
deck profile `LEVEL=1`, zero body effect, and no junction-current contribution
to the DC channel equation.
-/

namespace LeanModels.Spice

/-- Supported DC parameters of the MOS1 channel equation. `threshold` is the
positive normalized threshold magnitude for either polarity. -/
structure Mos1Params where
  polarity : MosPolarity
  threshold : ℝ
  beta : ℝ
  lambda : ℝ

/-- Look up one exact model parameter by its case-normalized name. -/
def MosModel.parameter? (model : MosModel) (name : String) : Option Rat :=
  model.parameters.toList.findSome? fun parameter =>
    if parameter.name == name then some parameter.value else none

/-- Find the complete structured model declaration referenced by a device. -/
def Netlist.findMosModelCard (netlist : Netlist)
    (name : String) : Option MosModel :=
  netlist.cards.toList.findSome? fun
    | .mosModel model => if model.name == name then some model else none
    | _ => none

/-- Interpret exactly the supported ngspice MOS1 profile. Device dimensions
are omitted in the example decks, so ngspice's default `W/L = 1` makes
`beta = KP`. Threshold is normalized to a positive magnitude for PMOS.
`IS=0` is required because junction-current equations are outside this
restricted channel-only profile. -/
noncomputable def Mos1Params.ofModel? (model : MosModel) : Option Mos1Params := do
  let level ← model.parameter? "level"
  if level != 1 then none else
  let vto ← model.parameter? "vto"
  let beta ← model.parameter? "kp"
  let lambda ← model.parameter? "lambda"
  let junctionSaturation ← model.parameter? "is"
  if junctionSaturation != 0 then none else
  let threshold : ℝ :=
    match model.polarity with
    | .nmos => (vto : ℝ)
    | .pmos => -(vto : ℝ)
  pure {
    polarity := model.polarity
    threshold
    beta := (beta : ℝ)
    lambda := (lambda : ℝ) }

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

/-- Real-valued DC state for a MOS1 circuit. The current associated with a
voltage source is positive from its first terminal to its second terminal. -/
structure Mos1CircuitState where
  voltage : String → ℝ
  sourceCurrent : String → ℝ

/-- The drain-to-source current of one MOS card, using the source orientation
written in the deck. PMOS channel current has the opposite conventional sign. -/
noncomputable def mos1DrainCurrent (netlist : Netlist)
    (state : Mos1CircuitState) (mosfet : Mosfet) : ℝ :=
  match netlist.findMosModelCard mosfet.model >>= Mos1Params.ofModel? with
  | none => 0
  | some params =>
      match params.polarity with
      | .nmos =>
          mos1ForwardCurrent params
            (state.voltage mosfet.gate - state.voltage mosfet.source)
            (state.voltage mosfet.drain - state.voltage mosfet.source)
      | .pmos =>
          -mos1ForwardCurrent params
            (state.voltage mosfet.source - state.voltage mosfet.gate)
            (state.voltage mosfet.source - state.voltage mosfet.drain)

/-- Current leaving one node through one supported MOS1-tier card. MOS gate
and bulk currents are zero in this restricted DC channel model. -/
noncomputable def mos1CardCurrentLeaving (netlist : Netlist)
    (state : Mos1CircuitState) (node : String) : Card → ℝ
  | .element element =>
      match element.kind with
      | .vsource =>
          if node == element.n1 then state.sourceCurrent element.name
          else if node == element.n2 then -state.sourceCurrent element.name
          else 0
      | _ => 0
  | .mosfet mosfet =>
      if node == mosfet.drain then mos1DrainCurrent netlist state mosfet
      else if node == mosfet.source then -mos1DrainCurrent netlist state mosfet
      else 0
  | _ => 0

/-- Total current leaving a named node. -/
noncomputable def mos1Kcl (netlist : Netlist)
    (state : Mos1CircuitState) (node : String) : ℝ :=
  netlist.cards.toList.foldl
    (fun total card => total + mos1CardCurrentLeaving netlist state node card) 0

/-- Nodes mentioned by cards whose currents participate in the MOS1 DC
semantics. Duplicates are harmless in the universal KCL condition. -/
def mos1CardNodes : Card → List String
  | .element element => [element.n1, element.n2]
  | .mosfet mosfet =>
      [mosfet.drain, mosfet.gate, mosfet.source, mosfet.bulk]
  | _ => []

def mos1Nodes (netlist : Netlist) : List String :=
  netlist.cards.toList.flatMap mos1CardNodes

/-- Constitutive and operating-region requirements for one flattened card. -/
noncomputable def Mos1CardLaw (netlist : Netlist)
    (state : Mos1CircuitState) : Card → Prop
  | .element element =>
      match element.kind with
      | .vsource =>
          state.voltage element.n1 - state.voltage element.n2 =
            (element.value : ℝ)
      | _ => False
  | .mosfet mosfet =>
      match netlist.findMosModelCard mosfet.model >>= Mos1Params.ofModel? with
      | none => False
      | some params =>
          match params.polarity with
          | .nmos =>
              0 ≤ state.voltage mosfet.drain - state.voltage mosfet.source
          | .pmos =>
              0 ≤ state.voltage mosfet.source - state.voltage mosfet.drain
  | .mosModel model => (Mos1Params.ofModel? model).isSome
  | .op _ => True
  | .xInstance _ | .unsupported _ | .subckt _ => False

/-- The ngspice Level-1 DC semantics used by the proofs:

* hierarchy is expanded without discarding MOS cards;
* every source and channel satisfies its constitutive equation;
* ground is zero;
* KCL holds at every non-ground terminal node.

Junction currents, body effect, capacitance, and geometry-dependent corrections
are deliberately outside this named profile. -/
noncomputable def Mos1Satisfies
    (netlist : Netlist) (state : Mos1CircuitState) : Prop :=
  match flattenSwitch netlist with
  | .error _ => False
  | .ok flat =>
      state.voltage "0" = 0 ∧
      (∀ card ∈ flat.cards.toList, Mos1CardLaw flat state card) ∧
      ∀ node ∈ mos1Nodes flat, node ≠ "0" → mos1Kcl flat state node = 0

/-- An operating envelope for static CMOS proofs. This is a named theorem
precondition, not an axiom: all observed nodes must remain between the supply
rails. -/
def Mos1WithinSupply
    (netlist : Netlist) (state : Mos1CircuitState) : Prop :=
  match flattenSwitch netlist with
  | .error _ => False
  | .ok flat =>
      ∀ node ∈ mos1Nodes flat, 0 ≤ state.voltage node ∧ state.voltage node ≤ 5

/-- Exact voltage associated with a Boolean input or output. -/
def logicVoltage : Bool → ℝ
  | false => 0
  | true => 5

/-- Ideal external voltage drivers for a two-input MOS1 block. -/
def Mos1DrivesTwo (state : Mos1CircuitState)
    (leftName rightName : String) (left right : Bool) : Prop :=
  state.voltage "0" = 0 ∧
  state.voltage "vdd" = 5 ∧
  state.voltage leftName = logicVoltage left ∧
  state.voltage rightName = logicVoltage right

/-- Soundness contract for an extracted two-input block under the MOS1
equations and the explicitly named static-CMOS supply envelope. -/
noncomputable def Mos1BinaryGateContract (netlist : Netlist)
    (leftName rightName outputName : String)
    (operation : Bool → Bool → Bool) : Prop :=
  ∀ left right state,
    Mos1Satisfies netlist state →
    Mos1WithinSupply netlist state →
    Mos1DrivesTwo state leftName rightName left right →
    state.voltage outputName = logicVoltage (operation left right)

/-- Soundness contract for a MOS1 half-adder. -/
noncomputable def Mos1HalfAdderContract (netlist : Netlist)
    (leftName rightName sumName carryName : String) : Prop :=
  ∀ left right state,
    Mos1Satisfies netlist state →
    Mos1WithinSupply netlist state →
    Mos1DrivesTwo state leftName rightName left right →
    state.voltage sumName = logicVoltage (Bool.xor left right) ∧
      state.voltage carryName = logicVoltage (Bool.and left right)

/-- One rail-valued observation of a physical MOS1 half-adder instance. -/
noncomputable def Mos1HalfAdderObservation (netlist : Netlist)
    (leftName rightName sumName carryName : String)
    (left right sum carry : Bool) : Prop :=
  ∃ state,
    Mos1Satisfies netlist state ∧
    Mos1WithinSupply netlist state ∧
    Mos1DrivesTwo state leftName rightName left right ∧
    state.voltage sumName = logicVoltage sum ∧
    state.voltage carryName = logicVoltage carry

theorem logicVoltage_injective : Function.Injective logicVoltage := by
  intro left right h
  rcases left with _ | _ <;> rcases right with _ | _ <;>
    simp [logicVoltage] at h ⊢

/-- A proved physical half-adder contract refines each observable instance to
the implementation-independent Boolean half-adder behavior. -/
theorem Mos1HalfAdderContract.observation_sound
    {netlist : Netlist} {leftName rightName sumName carryName : String}
    (hcontract :
      Mos1HalfAdderContract netlist leftName rightName sumName carryName)
    {left right sum carry : Bool}
    (hobservation :
      Mos1HalfAdderObservation netlist leftName rightName sumName carryName
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
