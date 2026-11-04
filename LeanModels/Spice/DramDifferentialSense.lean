import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Tactic
import LeanModels.Circuit.Equation
import LeanModels.Circuit.Transient
import LeanModels.Circuit.World
import LeanModels.Spice.Mos1

/-!
# Source-backed differential DRAM sense amplifier

The physical component is a pair of cross-coupled CMOS inverters with one
explicit load capacitor on each internal node. Its transient semantics is the
two-node KCL DAE generated below. The component has two stable rail
equilibria and, in the matched MOS1 model, a metastable common-mode
equilibrium. No sense decision or settling endpoint is included in the
behavior relation.
-/

namespace LeanModels.Spice

open LeanModels.Circuit

/-! ## Checked source projection -/

structure DramDifferentialSenseLayout where
  trueLine : LeanModels.Circuit.NodeId
  complementLine : LeanModels.Circuit.NodeId
  supply : LeanModels.Circuit.NodeId
  ground : LeanModels.Circuit.NodeId
  truePmos : LeanModels.Circuit.DeviceId
  trueNmos : LeanModels.Circuit.DeviceId
  complementPmos : LeanModels.Circuit.DeviceId
  complementNmos : LeanModels.Circuit.DeviceId
  trueCapacitor : LeanModels.Circuit.DeviceId
  complementCapacitor : LeanModels.Circuit.DeviceId
  nThreshold : Rat
  pThreshold : Rat
  nBeta : Rat
  pBeta : Rat
  trueCapacitance : Rat
  complementCapacitance : Rat
deriving Repr, Inhabited

private def senseNode
    (circuit : ElaboratedCircuit) (name : String) :
    Except String LeanModels.Circuit.NodeId :=
  match circuit.node? name with
  | some node => .ok node
  | none => .error s!"differential sense amplifier is missing node '{name}'"

private def senseDevice
    (circuit : ElaboratedCircuit) (name : String) :
    Except String (LeanModels.Circuit.DeviceId × ElaboratedDevice) := do
  let id ← match circuit.device? name with
    | some id => pure id
    | none =>
        throw s!"differential sense amplifier is missing device '{name}'"
  let device ← match circuit.devices[id.index]? with
    | some device => pure device
    | none => throw s!"device '{name}' has an invalid typed identifier"
  pure (id, device)

private def senseModel
    (circuit : ElaboratedCircuit) (id : LeanModels.Circuit.ModelId)
    (expected : MosPolarity) : Except String ElaboratedMos1Model := do
  let model ← match circuit.models[id.index]? with
    | some (.mos1 model) => pure model
    | none => throw "differential sense amplifier references a missing model"
  unless model.polarity == expected do
    throw "differential sense amplifier model polarity mismatch"
  unless model.channelLengthModulation == 0 &&
      model.junctionSaturation == 0 do
    throw "differential sense amplifier is outside the proved MOS1 profile"
  pure model

private def senseMosfet
    (circuit : ElaboratedCircuit) (name : String)
    (drain gate source bulk : LeanModels.Circuit.NodeId) :
    Except String
      (LeanModels.Circuit.DeviceId × LeanModels.Circuit.ModelId) := do
  let (id, device) ← senseDevice circuit name
  match device with
  | .mosfet _ actualDrain actualGate actualSource actualBulk model =>
      unless actualDrain == drain && actualGate == gate &&
          actualSource == source && actualBulk == bulk do
        throw s!"device '{name}' has the wrong terminal connectivity"
      pure (id, model)
  | _ => throw s!"device '{name}' is not a MOSFET"

private def senseCapacitor
    (circuit : ElaboratedCircuit) (name : String)
    (positive negative : LeanModels.Circuit.NodeId) :
    Except String (LeanModels.Circuit.DeviceId × Rat) := do
  let (id, device) ← senseDevice circuit name
  match device with
  | .capacitor _ actualPositive actualNegative capacitance =>
      unless actualPositive == positive && actualNegative == negative do
        throw s!"device '{name}' has the wrong terminal connectivity"
      pure (id, capacitance)
  | _ => throw s!"device '{name}' is not a capacitor"

/-- Recognize the exact flattened topology of the repository-owned
cross-coupled sense-amplifier deck and project all semantic parameters from
that source term. -/
def ElaboratedCircuit.toDramDifferentialSense
    (circuit : ElaboratedCircuit) :
    Except String DramDifferentialSenseLayout := do
  unless circuit.devices.size == 6 do
    throw s!"differential sense amplifier requires six devices, found {circuit.devices.size}"
  unless circuit.models.size == 2 do
    throw s!"differential sense amplifier requires two models, found {circuit.models.size}"
  let trueLine ← senseNode circuit "q"
  let complementLine ← senseNode circuit "qb"
  let supply ← senseNode circuit "vdd"
  let ground ← senseNode circuit "0"
  unless circuit.ground == ground do
    throw "differential sense amplifier ground mismatch"
  let (truePmos, truePModel) ←
    senseMosfet circuit "xsense.mpq"
      trueLine complementLine supply supply
  let (trueNmos, trueNModel) ←
    senseMosfet circuit "xsense.mnq"
      trueLine complementLine ground ground
  let (complementPmos, complementPModel) ←
    senseMosfet circuit "xsense.mpqb"
      complementLine trueLine supply supply
  let (complementNmos, complementNModel) ←
    senseMosfet circuit "xsense.mnqb"
      complementLine trueLine ground ground
  unless truePModel == complementPModel &&
      trueNModel == complementNModel do
    throw "cross-coupled halves do not share their declared models"
  let pModel ← senseModel circuit truePModel .pmos
  let nModel ← senseModel circuit trueNModel .nmos
  let (trueCapacitor, trueCapacitance) ←
    senseCapacitor circuit "xsense.cq" trueLine ground
  let (complementCapacitor, complementCapacitance) ←
    senseCapacitor circuit "xsense.cqb" complementLine ground
  pure
    { trueLine
      complementLine
      supply
      ground
      truePmos
      trueNmos
      complementPmos
      complementNmos
      trueCapacitor
      complementCapacitor
      nThreshold := nModel.threshold
      pThreshold := pModel.threshold
      nBeta := nModel.transconductance
      pBeta := pModel.transconductance
      trueCapacitance
      complementCapacitance }

/-! ## Primitive DAE semantics -/

inductive DramDifferentialSenseIndex
  | trueLine
  | complementLine
deriving Repr, DecidableEq, BEq, Inhabited

structure DramDifferentialSenseInstance where
  nThreshold : ℝ
  pThreshold : ℝ
  nBeta : ℝ
  pBeta : ℝ
  trueCapacitance : ℝ
  complementCapacitance : ℝ

noncomputable def nominalDramDifferentialSenseInstance :
    DramDifferentialSenseInstance :=
  { nThreshold := 1
    pThreshold := 1
    nBeta := 1 / 10000
    pBeta := 1 / 10000
    trueCapacitance := 3 / 10000000000000
    complementCapacitance := 3 / 10000000000000 }

structure DramDifferentialSenseEnvironment where
  supply : ℝ
  initialTrue : ℝ
  initialComplement : ℝ
  horizon : ℝ

abbrev DramDifferentialSenseWorld :=
  RunWorld DramDifferentialSenseInstance
    DramDifferentialSenseEnvironment Unit Unit

structure DramDifferentialSenseBoundary where
  voltage : VectorTrace DramDifferentialSenseIndex

noncomputable def DramDifferentialSenseLayout.fabricated
    (layout : DramDifferentialSenseLayout) :
    DramDifferentialSenseInstance :=
  { nThreshold := layout.nThreshold
    pThreshold := layout.pThreshold
    nBeta := layout.nBeta
    pBeta := layout.pBeta
    trueCapacitance := layout.trueCapacitance
    complementCapacitance := layout.complementCapacitance }

def DramDifferentialSenseAdmissible
    (world : DramDifferentialSenseWorld) : Prop :=
  0 < world.environment.supply ∧
  0 ≤ world.fabricated.nThreshold ∧
  0 ≤ world.fabricated.pThreshold ∧
  0 < world.fabricated.nBeta ∧
  0 < world.fabricated.pBeta ∧
  0 < world.fabricated.trueCapacitance ∧
  0 < world.fabricated.complementCapacitance ∧
  0 ≤ world.environment.initialTrue ∧
  world.environment.initialTrue ≤ world.environment.supply ∧
  0 ≤ world.environment.initialComplement ∧
  world.environment.initialComplement ≤ world.environment.supply ∧
  0 ≤ world.environment.horizon

noncomputable def dramDifferentialSenseNCurrent
    (fabricated : DramDifferentialSenseInstance)
    (gate output : ℝ) : ℝ :=
  mos1ForwardCurrent
    { polarity := .nmos
      threshold := fabricated.nThreshold
      beta := fabricated.nBeta
      lambda := 0 }
    gate output

noncomputable def dramDifferentialSensePCurrent
    (fabricated : DramDifferentialSenseInstance)
    (supply gate output : ℝ) : ℝ :=
  mos1ForwardCurrent
    { polarity := .pmos
      threshold := fabricated.pThreshold
      beta := fabricated.pBeta
      lambda := 0 }
    (supply - gate) (supply - output)

/-- With matched N/P parameters, a PMOS pull-up current is the complementary
NMOS current. This is the device-law symmetry behind preservation of the
balanced latch manifold. -/
theorem dramDifferentialSensePCurrent_eq_complementNCurrent
    {fabricated : DramDifferentialSenseInstance}
    (supply gate output : ℝ)
    (hThreshold : fabricated.nThreshold = fabricated.pThreshold)
    (hBeta : fabricated.nBeta = fabricated.pBeta) :
    dramDifferentialSensePCurrent fabricated supply gate output =
      dramDifferentialSenseNCurrent fabricated
        (supply - gate) (supply - output) := by
  unfold dramDifferentialSensePCurrent
    dramDifferentialSenseNCurrent mos1ForwardCurrent
  rw [hThreshold, hBeta]

/-- Two capacitor KCL equations for the cross-coupled latch. Currents leaving
each node through its NMOS are positive; PMOS currents enter the node. -/
noncomputable def dramDifferentialSenseDAE :
    VectorDAE DramDifferentialSenseWorld DramDifferentialSenseIndex where
  residual world _time state derivative :=
    world.fabricated.trueCapacitance * derivative .trueLine +
        dramDifferentialSenseNCurrent world.fabricated
          (state .complementLine) (state .trueLine) -
        dramDifferentialSensePCurrent world.fabricated
          world.environment.supply
          (state .complementLine) (state .trueLine) = 0 ∧
      world.fabricated.complementCapacitance *
          derivative .complementLine +
        dramDifferentialSenseNCurrent world.fabricated
          (state .trueLine) (state .complementLine) -
        dramDifferentialSensePCurrent world.fabricated
          world.environment.supply
          (state .trueLine) (state .complementLine) = 0

/-- Positive node capacitances make the primitive vector residual inhabited
at every state: each KCL equation directly determines its node derivative.
This is the pointwise non-vacuity companion for local DAE theorems. -/
theorem dramDifferentialSense_residual_realizable
    {world : DramDifferentialSenseWorld} {time : ℝ}
    {state : VectorState DramDifferentialSenseIndex}
    (hTrueCapacitance : 0 < world.fabricated.trueCapacitance)
    (hComplementCapacitance :
      0 < world.fabricated.complementCapacitance) :
    ∃ derivative : VectorState DramDifferentialSenseIndex,
      dramDifferentialSenseDAE.residual world time state derivative := by
  let derivative : VectorState DramDifferentialSenseIndex
    | .trueLine =>
        (dramDifferentialSensePCurrent world.fabricated
            world.environment.supply
            (state .complementLine) (state .trueLine) -
          dramDifferentialSenseNCurrent world.fabricated
            (state .complementLine) (state .trueLine)) /
          world.fabricated.trueCapacitance
    | .complementLine =>
        (dramDifferentialSensePCurrent world.fabricated
            world.environment.supply
            (state .trueLine) (state .complementLine) -
          dramDifferentialSenseNCurrent world.fabricated
            (state .trueLine) (state .complementLine)) /
          world.fabricated.complementCapacitance
  refine ⟨derivative, ?_⟩
  constructor
  · dsimp [dramDifferentialSenseDAE, derivative]
    field_simp [ne_of_gt hTrueCapacitance]
    ring
  · dsimp [dramDifferentialSenseDAE, derivative]
    field_simp [ne_of_gt hComplementCapacitance]
    ring

inductive DramDifferentialSenseClause where
  | initialTrue
  | initialComplement
  | evolution
deriving Repr, DecidableEq

noncomputable def DramDifferentialSenseProgram :
    EquationProgram DramDifferentialSenseClause
      DramDifferentialSenseWorld DramDifferentialSenseBoundary Unit where
  origin
    | .initialTrue => .initialCondition "true bitline voltage"
    | .initialComplement => .initialCondition "complement bitline voltage"
    | .evolution =>
        .evolution "cross-coupled MOS1 capacitor-KCL vector DAE"
  equation clause world boundary _internal :=
    match clause with
    | .initialTrue =>
        boundary.voltage 0 .trueLine = world.environment.initialTrue
    | .initialComplement =>
        boundary.voltage 0 .complementLine =
          world.environment.initialComplement
    | .evolution =>
        dramDifferentialSenseDAE.ACBehavesOn world
          world.environment.horizon boundary.voltage

noncomputable def DramDifferentialSenseBehavior :
    Behavior DramDifferentialSenseWorld
      DramDifferentialSenseBoundary Unit :=
  DramDifferentialSenseProgram.behavior

theorem dramDifferentialSenseProgram_physicsOnly :
    DramDifferentialSenseProgram.PhysicsOnly := by
  intro clause
  cases clause <;> rfl

noncomputable def dramDifferentialSenseRailState
    (supply : ℝ) (value : Bool) :
    VectorState DramDifferentialSenseIndex
  | .trueLine => if value then supply else 0
  | .complementLine => if value then 0 else supply

noncomputable def dramDifferentialSenseMetastableState
    (supply : ℝ) : VectorState DramDifferentialSenseIndex :=
  fun _index => supply / 2

noncomputable def dramDifferentialSenseBalancedState
    (supply deviation : ℝ) :
    VectorState DramDifferentialSenseIndex
  | .trueLine => supply / 2 + deviation
  | .complementLine => supply / 2 - deviation

/-- The physical rail rectangle for one instantaneous two-node state. This
is a model-validity domain, not a behavior equation or a sense
specification. -/
def DramDifferentialSenseStateInRailDomain
    (world : DramDifferentialSenseWorld)
    (state : VectorState DramDifferentialSenseIndex) : Prop :=
  0 ≤ state .trueLine ∧
  state .trueLine ≤ world.environment.supply ∧
  0 ≤ state .complementLine ∧
  state .complementLine ≤ world.environment.supply

/-- Signed differential coordinate of an arbitrary two-node state. -/
noncomputable def dramDifferentialSenseStateDeviation
    (state : VectorState DramDifferentialSenseIndex) : ℝ :=
  (state .trueLine - state .complementLine) / 2

/-- Dense differential-coordinate projection of an arbitrary two-node
trajectory. -/
noncomputable def dramDifferentialSenseTraceDeviation
    (trace : VectorTrace DramDifferentialSenseIndex) :
    DenseTrace ℝ :=
  fun time => dramDifferentialSenseStateDeviation (trace time)

/-- A state whose two node voltages sum to the supply is exactly the balanced
state represented by its differential coordinate. -/
theorem dramDifferentialSense_state_eq_balanced_of_sum
    {world : DramDifferentialSenseWorld}
    {state : VectorState DramDifferentialSenseIndex}
    (hsum :
      state .trueLine + state .complementLine =
        world.environment.supply) :
    state =
      dramDifferentialSenseBalancedState
        world.environment.supply
        (dramDifferentialSenseStateDeviation state) := by
  funext index
  cases index <;>
    simp [dramDifferentialSenseBalancedState,
      dramDifferentialSenseStateDeviation] <;>
    linarith

/-- The exact differential-mode rate obtained from the true-line KCL
equation on the balanced manifold. This is a derived view of the primitive
MOS/capacitor DAE, not an additional behavior clause. -/
noncomputable def dramDifferentialSenseBalancedRate
    (world : DramDifferentialSenseWorld) (deviation : ℝ) : ℝ :=
  (dramDifferentialSensePCurrent world.fabricated
      world.environment.supply
      (world.environment.supply / 2 - deviation)
      (world.environment.supply / 2 + deviation) -
    dramDifferentialSenseNCurrent world.fabricated
      (world.environment.supply / 2 - deviation)
      (world.environment.supply / 2 + deviation)) /
    world.fabricated.trueCapacitance

/-- For matched N/P channel laws and equal load capacitors, the primitive
two-node DAE restricted to the balanced manifold is exactly the scalar
differential-mode equation. Both directions are proved: the scalar view
neither adds behaviors nor loses primitive residual solutions on this
manifold. -/
theorem dramDifferentialSense_balanced_residual_iff
    {world : DramDifferentialSenseWorld} {time deviation : ℝ}
    {derivative : VectorState DramDifferentialSenseIndex}
    (hThreshold :
      world.fabricated.nThreshold = world.fabricated.pThreshold)
    (hBeta : world.fabricated.nBeta = world.fabricated.pBeta)
    (hCapacitance :
      world.fabricated.trueCapacitance =
        world.fabricated.complementCapacitance)
    (hCapacitancePositive :
      0 < world.fabricated.trueCapacitance) :
    dramDifferentialSenseDAE.residual world time
        (dramDifferentialSenseBalancedState
          world.environment.supply deviation)
        derivative ↔
      derivative .trueLine =
          dramDifferentialSenseBalancedRate world deviation ∧
        derivative .complementLine =
          -dramDifferentialSenseBalancedRate world deviation := by
  have hPTrue :
      dramDifferentialSensePCurrent world.fabricated
          world.environment.supply
          (world.environment.supply / 2 - deviation)
          (world.environment.supply / 2 + deviation) =
        dramDifferentialSenseNCurrent world.fabricated
          (world.environment.supply / 2 + deviation)
          (world.environment.supply / 2 - deviation) := by
    unfold dramDifferentialSensePCurrent
      dramDifferentialSenseNCurrent mos1ForwardCurrent
    rw [← hThreshold, ← hBeta]
    ring_nf
  have hPComplement :
      dramDifferentialSensePCurrent world.fabricated
          world.environment.supply
          (world.environment.supply / 2 + deviation)
          (world.environment.supply / 2 - deviation) =
        dramDifferentialSenseNCurrent world.fabricated
          (world.environment.supply / 2 - deviation)
          (world.environment.supply / 2 + deviation) := by
    unfold dramDifferentialSensePCurrent
      dramDifferentialSenseNCurrent mos1ForwardCurrent
    rw [← hThreshold, ← hBeta]
    ring_nf
  simp only [dramDifferentialSenseDAE,
    dramDifferentialSenseBalancedState]
  rw [hCapacitance]
  unfold dramDifferentialSenseBalancedRate
  rw [hCapacitance]
  rw [hPTrue, hPComplement]
  have hComplementCapacitancePositive :
      0 < world.fabricated.complementCapacitance := by
    rw [← hCapacitance]
    exact hCapacitancePositive
  have hComplementCapacitanceNe :
      world.fabricated.complementCapacitance ≠ 0 :=
    ne_of_gt hComplementCapacitancePositive
  constructor
  · rintro ⟨hTrue, hComplement⟩
    field_simp [hComplementCapacitanceNe]
    constructor <;>
      field_simp [hComplementCapacitanceNe] at hTrue hComplement ⊢ <;>
      ring_nf at hTrue hComplement ⊢ <;>
      linarith
  · rintro ⟨hTrue, hComplement⟩
    constructor <;>
      field_simp [hComplementCapacitanceNe] at hTrue hComplement ⊢ <;>
      ring_nf at hTrue hComplement ⊢ <;>
      linarith

/-- Inside the rail rectangle, the primitive matched-latch KCL equations
dissipate squared common-mode error. In particular, the derivative of
`(vtrue + vcomplement - VDD)^2` is nonpositive at every residual point.

This is derived only from the four MOS1 laws, equal capacitors, and KCL. It
does not assume that the state is balanced. -/
theorem dramDifferentialSense_common_mode_dissipates
    {world : DramDifferentialSenseWorld} {time : ℝ}
    {state derivative : VectorState DramDifferentialSenseIndex}
    (hThreshold :
      world.fabricated.nThreshold = world.fabricated.pThreshold)
    (hBeta : world.fabricated.nBeta = world.fabricated.pBeta)
    (hBetaNonnegative : 0 ≤ world.fabricated.nBeta)
    (hCapacitance :
      world.fabricated.trueCapacitance =
        world.fabricated.complementCapacitance)
    (hCapacitancePositive :
      0 < world.fabricated.trueCapacitance)
    (hstate :
      DramDifferentialSenseStateInRailDomain world state)
    (hresidual :
      dramDifferentialSenseDAE.residual world time state derivative) :
    (state .trueLine + state .complementLine -
        world.environment.supply) *
      (derivative .trueLine + derivative .complementLine) ≤ 0 := by
  let supply := world.environment.supply
  let trueVoltage := state .trueLine
  let complementVoltage := state .complementLine
  let error := trueVoltage + complementVoltage - supply
  change
    error * (derivative .trueLine + derivative .complementLine) ≤ 0
  change
    0 ≤ trueVoltage ∧ trueVoltage ≤ supply ∧
      0 ≤ complementVoltage ∧ complementVoltage ≤ supply at hstate
  have htrueReflection :
      supply - complementVoltage = trueVoltage - error := by
    dsimp [error]
    ring
  have hcomplementReflection :
      supply - trueVoltage = complementVoltage - error := by
    dsimp [error]
    ring
  have htrueP :
      dramDifferentialSensePCurrent world.fabricated
          supply complementVoltage trueVoltage =
        dramDifferentialSenseNCurrent world.fabricated
          (supply - complementVoltage) (supply - trueVoltage) :=
    dramDifferentialSensePCurrent_eq_complementNCurrent
      supply complementVoltage trueVoltage hThreshold hBeta
  have hcomplementP :
      dramDifferentialSensePCurrent world.fabricated
          supply trueVoltage complementVoltage =
        dramDifferentialSenseNCurrent world.fabricated
          (supply - trueVoltage) (supply - complementVoltage) :=
    dramDifferentialSensePCurrent_eq_complementNCurrent
      supply trueVoltage complementVoltage hThreshold hBeta
  have htrueKcl :
      world.fabricated.trueCapacitance *
          derivative .trueLine +
        dramDifferentialSenseNCurrent world.fabricated
          complementVoltage trueVoltage -
        dramDifferentialSenseNCurrent world.fabricated
          (supply - complementVoltage) (supply - trueVoltage) = 0 := by
    simpa [dramDifferentialSenseDAE, supply, trueVoltage,
      complementVoltage, htrueP] using hresidual.1
  have hcomplementKcl :
      world.fabricated.trueCapacitance *
          derivative .complementLine +
        dramDifferentialSenseNCurrent world.fabricated
          trueVoltage complementVoltage -
        dramDifferentialSenseNCurrent world.fabricated
          (supply - trueVoltage) (supply - complementVoltage) = 0 := by
    have hkcl := hresidual.2
    rw [← hCapacitance] at hkcl
    simpa [dramDifferentialSenseDAE, supply, trueVoltage,
      complementVoltage, hcomplementP] using hkcl
  rcases le_total 0 error with herror | herror
  · have htrueCurrent :
        dramDifferentialSenseNCurrent world.fabricated
            (supply - complementVoltage) (supply - trueVoltage) ≤
          dramDifferentialSenseNCurrent world.fabricated
            trueVoltage complementVoltage := by
      unfold dramDifferentialSenseNCurrent
      rw [htrueReflection, hcomplementReflection]
      exact mos1ForwardCurrent_mono_common_shift
        .nmos world.fabricated.nThreshold world.fabricated.nBeta
        trueVoltage complementVoltage error
        hBetaNonnegative herror
        (by rw [← hcomplementReflection]; linarith)
    have hcomplementCurrent :
        dramDifferentialSenseNCurrent world.fabricated
            (supply - trueVoltage) (supply - complementVoltage) ≤
          dramDifferentialSenseNCurrent world.fabricated
            complementVoltage trueVoltage := by
      unfold dramDifferentialSenseNCurrent
      rw [hcomplementReflection, htrueReflection]
      exact mos1ForwardCurrent_mono_common_shift
        .nmos world.fabricated.nThreshold world.fabricated.nBeta
        complementVoltage trueVoltage error
        hBetaNonnegative herror
        (by rw [← htrueReflection]; linarith)
    have hderivative :
        derivative .trueLine + derivative .complementLine ≤ 0 := by
      nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos herror hderivative
  · have hshift : 0 ≤ -error := by linarith
    have htrueUnshift :
        supply - complementVoltage - -error = trueVoltage := by
      dsimp [error]
      ring
    have hcomplementUnshift :
        supply - trueVoltage - -error = complementVoltage := by
      dsimp [error]
      ring
    have htrueCurrent :
        dramDifferentialSenseNCurrent world.fabricated
            trueVoltage complementVoltage ≤
          dramDifferentialSenseNCurrent world.fabricated
            (supply - complementVoltage) (supply - trueVoltage) := by
      unfold dramDifferentialSenseNCurrent
      have hcurrent := mos1ForwardCurrent_mono_common_shift
          .nmos world.fabricated.nThreshold world.fabricated.nBeta
          (supply - complementVoltage) (supply - trueVoltage) (-error)
          hBetaNonnegative hshift
          (by rw [hcomplementUnshift]; exact hstate.2.2.1)
      simpa only [htrueUnshift, hcomplementUnshift] using hcurrent
    have hcomplementCurrent :
        dramDifferentialSenseNCurrent world.fabricated
            complementVoltage trueVoltage ≤
          dramDifferentialSenseNCurrent world.fabricated
            (supply - trueVoltage) (supply - complementVoltage) := by
      unfold dramDifferentialSenseNCurrent
      have hcurrent := mos1ForwardCurrent_mono_common_shift
          .nmos world.fabricated.nThreshold world.fabricated.nBeta
          (supply - trueVoltage) (supply - complementVoltage) (-error)
          hBetaNonnegative hshift
          (by rw [htrueUnshift]; exact hstate.1)
      simpa only [hcomplementUnshift, htrueUnshift] using hcurrent
    have hderivative :
        0 ≤ derivative .trueLine + derivative .complementLine := by
      nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg herror hderivative

/-- The exact scalar DAE capability induced by the primitive vector DAE on
the balanced manifold. Its relationship to the source-backed denotation is
certified by `dramDifferentialSense_balanced_residual_iff` and the lifting
theorem below. -/
noncomputable def dramDifferentialSenseBalancedDAE :
    ScalarDAE DramDifferentialSenseWorld where
  residual world _time deviation derivative :=
    derivative = dramDifferentialSenseBalancedRate world deviation

noncomputable def dramDifferentialSenseBalancedTrace
    (world : DramDifferentialSenseWorld) (deviation : DenseTrace ℝ) :
    VectorTrace DramDifferentialSenseIndex :=
  fun time =>
    dramDifferentialSenseBalancedState
      world.environment.supply (deviation time)

/-- Every scalar residual point has a simultaneous primitive derivative
vector. This is the local realizability companion to the residual reduction,
and prevents the derived universal statement from ranging over an empty
residual relation. -/
theorem dramDifferentialSense_balanced_residual_realizable
    {world : DramDifferentialSenseWorld} {time deviation : ℝ}
    (hThreshold :
      world.fabricated.nThreshold = world.fabricated.pThreshold)
    (hBeta : world.fabricated.nBeta = world.fabricated.pBeta)
    (hCapacitance :
      world.fabricated.trueCapacitance =
        world.fabricated.complementCapacitance)
    (hCapacitancePositive :
      0 < world.fabricated.trueCapacitance) :
    ∃ derivative : VectorState DramDifferentialSenseIndex,
      dramDifferentialSenseDAE.residual world time
        (dramDifferentialSenseBalancedState
          world.environment.supply deviation)
        derivative := by
  let rate := dramDifferentialSenseBalancedRate world deviation
  let derivative : VectorState DramDifferentialSenseIndex
    | .trueLine => rate
    | .complementLine => -rate
  refine ⟨derivative, ?_⟩
  apply (dramDifferentialSense_balanced_residual_iff
    hThreshold hBeta hCapacitance hCapacitancePositive).2
  exact ⟨rfl, rfl⟩

/-- A physical scalar trajectory lifts to a physical trajectory of the
source-backed two-node DAE. The theorem is one-way because an arbitrary
vector trajectory must separately prove that it stays on the balanced
manifold before it can be projected back to this view. -/
theorem dramDifferentialSense_balanced_ac_lift
    {world : DramDifferentialSenseWorld} {horizon : ℝ}
    {deviation : DenseTrace ℝ}
    (hThreshold :
      world.fabricated.nThreshold = world.fabricated.pThreshold)
    (hBeta : world.fabricated.nBeta = world.fabricated.pBeta)
    (hCapacitance :
      world.fabricated.trueCapacitance =
        world.fabricated.complementCapacitance)
    (hCapacitancePositive :
      0 < world.fabricated.trueCapacitance)
    (hscalar :
      dramDifferentialSenseBalancedDAE.ACBehavesOn
        world horizon deviation) :
    dramDifferentialSenseDAE.ACBehavesOn world horizon
      (dramDifferentialSenseBalancedTrace world deviation) := by
  refine ⟨hscalar.1, ?_, ?_⟩
  · intro index
    have hconstant :
        AbsolutelyContinuousOnInterval
          (fun _time : ℝ => world.environment.supply / 2)
          0 horizon :=
      (LipschitzWith.const (world.environment.supply / 2))
        |>.lipschitzOnWith
        |>.absolutelyContinuousOnInterval
    cases index
    · change AbsolutelyContinuousOnInterval
        (fun time =>
          world.environment.supply / 2 + deviation time)
        0 horizon
      exact hconstant.add hscalar.2.1
    · change AbsolutelyContinuousOnInterval
        (fun time =>
          world.environment.supply / 2 - deviation time)
        0 horizon
      exact hconstant.sub hscalar.2.1
  · filter_upwards [hscalar.2.2] with time htime
    rcases htime with ⟨rate, hderivative, hrate⟩
    let derivative : VectorState DramDifferentialSenseIndex
      | .trueLine => rate
      | .complementLine => -rate
    refine ⟨derivative, ?_, ?_⟩
    · intro index
      cases index
      · simpa [dramDifferentialSenseBalancedTrace,
          dramDifferentialSenseBalancedState, derivative] using
          hderivative.const_add (world.environment.supply / 2)
      · simpa [dramDifferentialSenseBalancedTrace,
          dramDifferentialSenseBalancedState, derivative] using
          hderivative.const_sub (world.environment.supply / 2)
    · apply (dramDifferentialSense_balanced_residual_iff
        hThreshold hBeta hCapacitance hCapacitancePositive).2
      exact ⟨hrate, congrArg Neg.neg hrate⟩

/-- Every rail-valid primitive two-node trajectory that starts on the
balanced manifold remains there for its complete finite horizon.

The proof integrates the nonpositive derivative of squared common-mode
error. Thus balance is selected by the primitive MOS/capacitor equations and
the initial condition; it is not assumed as a behavior clause. -/
theorem dramDifferentialSense_balanced_invariant_on_domain
    {world : DramDifferentialSenseWorld} {horizon : ℝ}
    {trace : VectorTrace DramDifferentialSenseIndex}
    (hThreshold :
      world.fabricated.nThreshold = world.fabricated.pThreshold)
    (hBeta : world.fabricated.nBeta = world.fabricated.pBeta)
    (hBetaNonnegative : 0 ≤ world.fabricated.nBeta)
    (hCapacitance :
      world.fabricated.trueCapacitance =
        world.fabricated.complementCapacitance)
    (hCapacitancePositive :
      0 < world.fabricated.trueCapacitance)
    (hbehavior :
      dramDifferentialSenseDAE.ACBehavesOn world horizon trace)
    (hdomain :
      ∀ time, 0 ≤ time → time ≤ horizon →
        DramDifferentialSenseStateInRailDomain world (trace time))
    (hinitial :
      trace 0 .trueLine + trace 0 .complementLine =
        world.environment.supply) :
    ∀ time, 0 ≤ time → time ≤ horizon →
      trace time .trueLine + trace time .complementLine =
        world.environment.supply := by
  let commonModeError : ℝ → ℝ :=
    (fun time =>
      trace time .trueLine + trace time .complementLine) -
      (fun _time => world.environment.supply)
  let energy : ℝ → ℝ := commonModeError * commonModeError
  have herrorAC :
      AbsolutelyContinuousOnInterval commonModeError 0 horizon := by
    have hadd :
        AbsolutelyContinuousOnInterval
          (fun time : ℝ =>
            trace time .trueLine + trace time .complementLine)
          0 horizon :=
      (hbehavior.2.1 .trueLine).add
        (hbehavior.2.1 .complementLine)
    have hconstant :
        AbsolutelyContinuousOnInterval
          (fun _time : ℝ => world.environment.supply) 0 horizon :=
      (LipschitzWith.const world.environment.supply).lipschitzOnWith
        |>.absolutelyContinuousOnInterval
    exact hadd.sub hconstant
  have henergyAC :
      AbsolutelyContinuousOnInterval energy 0 horizon :=
    herrorAC.mul herrorAC
  have henergyDerivative :
      ∀ᵐ point ∂MeasureTheory.volume.restrict
          (Set.uIcc (0 : ℝ) horizon),
        deriv energy point ≤ 0 := by
    filter_upwards [hbehavior.2.2,
      MeasureTheory.ae_restrict_mem measurableSet_uIcc]
      with point hpoint hpointDomain
    obtain ⟨derivative, hderivative, hresidual⟩ := hpoint
    rw [Set.uIcc_of_le hbehavior.1] at hpointDomain
    have hstate :=
      hdomain point hpointDomain.1 hpointDomain.2
    have herrorDerivative :
        HasDerivAt commonModeError
          (derivative .trueLine + derivative .complementLine)
          point := by
      have hadd : HasDerivAt
          (fun time : ℝ =>
            trace time .trueLine + trace time .complementLine)
          (derivative .trueLine + derivative .complementLine)
          point :=
        (hderivative .trueLine).add
          (hderivative .complementLine)
      have hconstant :
          HasDerivAt
            (fun _time : ℝ => world.environment.supply) 0 point :=
        hasDerivAt_const point world.environment.supply
      simpa only [commonModeError, sub_zero] using hadd.sub hconstant
    have hderivativeEnergy :
        HasDerivAt energy
          (2 * commonModeError point *
            (derivative .trueLine + derivative .complementLine))
          point := by
      have hmul := herrorDerivative.mul herrorDerivative
      apply hmul.congr_deriv
      ring
    have hdissipates :=
      dramDifferentialSense_common_mode_dissipates
        hThreshold hBeta hBetaNonnegative hCapacitance
        hCapacitancePositive hstate hresidual
    rw [hderivativeEnergy.deriv]
    change
      2 *
          (trace point .trueLine + trace point .complementLine -
            world.environment.supply) *
          (derivative .trueLine + derivative .complementLine) ≤
        0
    nlinarith
  intro time htime0 htimeHorizon
  have hsubinterval :
      Set.uIcc (0 : ℝ) time ⊆ Set.uIcc (0 : ℝ) horizon := by
    rw [Set.uIcc_of_le htime0, Set.uIcc_of_le hbehavior.1]
    intro point hpoint
    exact ⟨hpoint.1, hpoint.2.trans htimeHorizon⟩
  have henergyACSub :
      AbsolutelyContinuousOnInterval energy 0 time :=
    henergyAC.mono hsubinterval
  have henergyDerivativeSub :
      ∀ᵐ point ∂MeasureTheory.volume.restrict
          (Set.uIcc (0 : ℝ) time),
        deriv energy point ≤ 0 :=
    MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      hsubinterval henergyDerivative
  have hintegral :
      (∫ point in (0 : ℝ)..time, deriv energy point) ≤ 0 := by
    have hzero :
        IntervalIntegrable (fun _point : ℝ => (0 : ℝ))
          MeasureTheory.volume 0 time :=
      intervalIntegrable_const
    rw [Set.uIcc_of_le htime0] at henergyDerivativeSub
    simpa using
      intervalIntegral.integral_mono_ae_restrict htime0
        henergyACSub.intervalIntegrable_deriv hzero
        henergyDerivativeSub
  rw [henergyACSub.integral_deriv_eq_sub] at hintegral
  have hinitialError : commonModeError 0 = 0 := by
    dsimp [commonModeError]
    linarith
  have hinitialEnergy : energy 0 = 0 := by
    simp [energy, hinitialError]
  have henergyNonnegative : 0 ≤ energy time := by
    exact mul_self_nonneg _
  rw [hinitialEnergy] at hintegral
  have henergyZero : energy time = 0 := by
    linarith
  have herrorZero : commonModeError time = 0 :=
    mul_self_eq_zero.mp henergyZero
  dsimp [commonModeError] at herrorZero
  linarith

/-- Project a primitive vector trajectory known to remain balanced into the
exact scalar DAE capability. This is the reverse direction of
`dramDifferentialSense_balanced_ac_lift`. -/
theorem dramDifferentialSense_balanced_ac_project
    {world : DramDifferentialSenseWorld} {horizon : ℝ}
    {trace : VectorTrace DramDifferentialSenseIndex}
    (hThreshold :
      world.fabricated.nThreshold = world.fabricated.pThreshold)
    (hBeta : world.fabricated.nBeta = world.fabricated.pBeta)
    (hCapacitance :
      world.fabricated.trueCapacitance =
        world.fabricated.complementCapacitance)
    (hCapacitancePositive :
      0 < world.fabricated.trueCapacitance)
    (hbehavior :
      dramDifferentialSenseDAE.ACBehavesOn world horizon trace)
    (hbalanced :
      ∀ time, 0 ≤ time → time ≤ horizon →
        trace time .trueLine + trace time .complementLine =
          world.environment.supply) :
    dramDifferentialSenseBalancedDAE.ACBehavesOn world horizon
      (dramDifferentialSenseTraceDeviation trace) := by
  refine ⟨hbehavior.1, ?_, ?_⟩
  · have hdifference :=
      (hbehavior.2.1 .trueLine).sub
        (hbehavior.2.1 .complementLine)
    change AbsolutelyContinuousOnInterval
      (fun time : ℝ =>
        trace time .trueLine - trace time .complementLine)
      0 horizon at hdifference
    have hscaled := hdifference.const_mul (1 / 2)
    change AbsolutelyContinuousOnInterval
      (fun time : ℝ =>
        (1 / 2) *
          (trace time .trueLine - trace time .complementLine))
      0 horizon at hscaled
    change AbsolutelyContinuousOnInterval
      (fun time : ℝ =>
        (trace time .trueLine - trace time .complementLine) / 2)
      0 horizon
    simpa only [div_eq_mul_inv, one_div, one_mul, mul_comm] using hscaled
  · filter_upwards [hbehavior.2.2,
      MeasureTheory.ae_restrict_mem measurableSet_uIcc]
      with point hpoint hpointDomain
    obtain ⟨derivative, hderivative, hresidual⟩ := hpoint
    rw [Set.uIcc_of_le hbehavior.1] at hpointDomain
    have hsum :=
      hbalanced point hpointDomain.1 hpointDomain.2
    have hstate :=
      dramDifferentialSense_state_eq_balanced_of_sum
        (world := world) hsum
    let deviationDerivative :=
      (derivative .trueLine - derivative .complementLine) / 2
    refine ⟨deviationDerivative, ?_, ?_⟩
    · have hdifference :=
        (hderivative .trueLine).sub
          (hderivative .complementLine)
      change HasDerivAt
        (fun time : ℝ =>
          trace time .trueLine - trace time .complementLine)
        (derivative .trueLine - derivative .complementLine)
        point at hdifference
      have hscaled := hdifference.div_const 2
      change HasDerivAt
        (fun time : ℝ =>
          (trace time .trueLine - trace time .complementLine) / 2)
        deviationDerivative point
      simpa only [deviationDerivative] using hscaled
    · have hbalancedResidual :
          dramDifferentialSenseDAE.residual world point
            (dramDifferentialSenseBalancedState
              world.environment.supply
              (dramDifferentialSenseStateDeviation (trace point)))
            derivative := by
        rw [← hstate]
        exact hresidual
      have hrates :=
        (dramDifferentialSense_balanced_residual_iff
          hThreshold hBeta hCapacitance hCapacitancePositive).1
          hbalancedResidual
      change deviationDerivative =
        dramDifferentialSenseBalancedRate world
          (dramDifferentialSenseTraceDeviation trace point)
      dsimp [deviationDerivative,
        dramDifferentialSenseTraceDeviation]
      nlinarith [hrates.1, hrates.2]

/-- Exact reverse projection for every rail-valid primitive trajectory with a
balanced initial state. -/
theorem dramDifferentialSense_balanced_ac_project_on_domain
    {world : DramDifferentialSenseWorld} {horizon : ℝ}
    {trace : VectorTrace DramDifferentialSenseIndex}
    (hThreshold :
      world.fabricated.nThreshold = world.fabricated.pThreshold)
    (hBeta : world.fabricated.nBeta = world.fabricated.pBeta)
    (hBetaNonnegative : 0 ≤ world.fabricated.nBeta)
    (hCapacitance :
      world.fabricated.trueCapacitance =
        world.fabricated.complementCapacitance)
    (hCapacitancePositive :
      0 < world.fabricated.trueCapacitance)
    (hbehavior :
      dramDifferentialSenseDAE.ACBehavesOn world horizon trace)
    (hdomain :
      ∀ time, 0 ≤ time → time ≤ horizon →
        DramDifferentialSenseStateInRailDomain world (trace time))
    (hinitial :
      trace 0 .trueLine + trace 0 .complementLine =
        world.environment.supply) :
    dramDifferentialSenseBalancedDAE.ACBehavesOn world horizon
      (dramDifferentialSenseTraceDeviation trace) :=
  dramDifferentialSense_balanced_ac_project
    hThreshold hBeta hCapacitance hCapacitancePositive hbehavior
    (dramDifferentialSense_balanced_invariant_on_domain
      hThreshold hBeta hBetaNonnegative hCapacitance
      hCapacitancePositive hbehavior hdomain hinitial)

/-- Closed form of the source deck's balanced differential-mode field.

The three pieces are the MOS1 saturation/saturation,
triode/saturation, and triode/cutoff regions respectively. Adjacent formulas
agree at `deviation = 1/2` and `deviation = 3/2`; they are not empirical fit
curves. -/
noncomputable def dramDifferentialSenseNominalBalancedRate
    (deviation : ℝ) : ℝ :=
  if deviation ≤ 1 / 2 then
    1000000000 * deviation
  else if deviation ≤ 3 / 2 then
    (1000000000 / 3) *
      (-2 * deviation ^ 2 + 5 * deviation - 1 / 2)
  else
    (1000000000 / 3) *
      (-3 / 2 * deviation ^ 2 + 7 / 2 * deviation + 5 / 8)

/-- The three source-derived MOS regions join continuously. This is the
regularity prerequisite for constructing and uniquely continuing physical
trajectories across the region boundaries. -/
theorem dramDifferentialSenseNominalBalancedRate_continuous :
    Continuous dramDifferentialSenseNominalBalancedRate := by
  have hmiddle :
      Continuous fun deviation : ℝ =>
        if deviation ≤ 3 / 2 then
          (1000000000 / 3) *
            (-2 * deviation ^ 2 + 5 * deviation - 1 / 2)
        else
          (1000000000 / 3) *
            (-3 / 2 * deviation ^ 2 +
              7 / 2 * deviation + 5 / 8) := by
    apply Continuous.if_le
      (by fun_prop) (by fun_prop)
      continuous_id continuous_const
    intro deviation hboundary
    simp only [id_eq] at hboundary
    subst deviation
    norm_num
  unfold dramDifferentialSenseNominalBalancedRate
  apply Continuous.if_le
    (by fun_prop) hmiddle
    continuous_id continuous_const
  intro deviation hboundary
  simp only [id_eq] at hboundary
  subst deviation
  norm_num

/-- Complete source-derived differential field, including hypothetical
states outside the 0 V to 5 V rail envelope. The two negative-differential
regions are the mirror images of the positive regions. Keeping this extension
source-derived, rather than clamping it, is essential for a non-circular
validity-domain proof: a hypothetical escaping trajectory must still be
interpreted by the primitive equations while the proof rules out the escape. -/
noncomputable def dramDifferentialSenseNominalExtendedRate
    (deviation : ℝ) : ℝ :=
  if deviation ≤ -(3 / 2) then
    -(1000000000 / 3) *
      (-3 / 2 * (-deviation) ^ 2 +
        7 / 2 * (-deviation) + 5 / 8)
  else if deviation ≤ -(1 / 2) then
    -(1000000000 / 3) *
      (-2 * (-deviation) ^ 2 + 5 * (-deviation) - 1 / 2)
  else if deviation ≤ 1 / 2 then
    1000000000 * deviation
  else if deviation ≤ 3 / 2 then
    (1000000000 / 3) *
      (-2 * deviation ^ 2 + 5 * deviation - 1 / 2)
  else
    (1000000000 / 3) *
      (-3 / 2 * deviation ^ 2 + 7 / 2 * deviation + 5 / 8)

/-- The five source regions join continuously. -/
theorem dramDifferentialSenseNominalExtendedRate_continuous :
    Continuous dramDifferentialSenseNominalExtendedRate := by
  have hpositive :
      Continuous fun deviation : ℝ =>
        if deviation ≤ 3 / 2 then
          (1000000000 / 3) *
            (-2 * deviation ^ 2 + 5 * deviation - 1 / 2)
        else
          (1000000000 / 3) *
            (-3 / 2 * deviation ^ 2 +
              7 / 2 * deviation + 5 / 8) := by
    apply Continuous.if_le
      (by fun_prop) (by fun_prop)
      continuous_id continuous_const
    intro deviation hboundary
    simp only [id_eq] at hboundary
    subst deviation
    norm_num
  have hcenter :
      Continuous fun deviation : ℝ =>
        if deviation ≤ 1 / 2 then
          1000000000 * deviation
        else if deviation ≤ 3 / 2 then
          (1000000000 / 3) *
            (-2 * deviation ^ 2 + 5 * deviation - 1 / 2)
        else
          (1000000000 / 3) *
            (-3 / 2 * deviation ^ 2 +
              7 / 2 * deviation + 5 / 8) := by
    apply Continuous.if_le
      (by fun_prop) hpositive
      continuous_id continuous_const
    intro deviation hboundary
    simp only [id_eq] at hboundary
    subst deviation
    norm_num
  have hnegativeMiddle :
      Continuous fun deviation : ℝ =>
        if deviation ≤ -(1 / 2) then
          -(1000000000 / 3) *
            (-2 * (-deviation) ^ 2 +
              5 * (-deviation) - 1 / 2)
        else if deviation ≤ 1 / 2 then
          1000000000 * deviation
        else if deviation ≤ 3 / 2 then
          (1000000000 / 3) *
            (-2 * deviation ^ 2 + 5 * deviation - 1 / 2)
        else
          (1000000000 / 3) *
            (-3 / 2 * deviation ^ 2 +
              7 / 2 * deviation + 5 / 8) := by
    apply Continuous.if_le
      (by fun_prop) hcenter
      continuous_id continuous_const
    intro deviation hboundary
    simp only [id_eq] at hboundary
    subst deviation
    norm_num
  unfold dramDifferentialSenseNominalExtendedRate
  apply Continuous.if_le
    (by fun_prop) hnegativeMiddle
    continuous_id continuous_const
  intro deviation hboundary
  simp only [id_eq] at hboundary
  subst deviation
  norm_num

set_option maxHeartbeats 1600000 in
/-- The global five-region field is definitionally projected from the
primitive MOS1 currents. Unlike the closed-basin formula below, this theorem
has no rail-domain premise. -/
theorem dramDifferentialSense_nominal_extended_rate_eq
    {world : DramDifferentialSenseWorld} {deviation : ℝ}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000) :
    dramDifferentialSenseBalancedRate world deviation =
      dramDifferentialSenseNominalExtendedRate deviation := by
  unfold dramDifferentialSenseNominalExtendedRate
    dramDifferentialSenseBalancedRate
    dramDifferentialSenseNCurrent
    dramDifferentialSensePCurrent
    mos1ForwardCurrent
  rw [hsupply, hnThreshold, hpThreshold, hnBeta, hpBeta, hTrueCap]
  norm_num
  split_ifs <;> nlinarith

/-- An absolutely-continuous physical trajectory of the nominal scalar DAE is
a classical ODE solution within the complete closed horizon. The upgrade is
derived, not assumed: absolute continuity gives the
fundamental-theorem-of-calculus identity, the almost-everywhere residual
replaces its derivative integrand by the continuous source field, and the
resulting integral has the stated pointwise derivative. -/
theorem dramDifferentialSense_nominal_scalar_hasDerivWithinAt
    {world : DramDifferentialSenseWorld}
    {trajectory : DenseTrace ℝ} {horizon time : ℝ}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000)
    (hbehavior :
      dramDifferentialSenseBalancedDAE.ACBehavesOn
        world horizon trajectory)
    (htime : time ∈ Set.Icc (0 : ℝ) horizon) :
    HasDerivWithinAt trajectory
      (dramDifferentialSenseNominalExtendedRate (trajectory time))
      (Set.Icc (0 : ℝ) horizon) time := by
  let fieldTrace : ℝ → ℝ := fun point =>
    dramDifferentialSenseNominalExtendedRate (trajectory point)
  let primitive : ℝ → ℝ := fun point =>
    trajectory 0 + ∫ t in (0 : ℝ)..point, fieldTrace t
  have htrajectoryContinuous :
      ContinuousOn trajectory (Set.Icc (0 : ℝ) horizon) := by
    have hcontinuous := hbehavior.2.1.continuousOn
    rwa [Set.uIcc_of_le hbehavior.1] at hcontinuous
  have hfieldTraceContinuous :
      ContinuousOn fieldTrace (Set.Icc (0 : ℝ) horizon) := by
    exact
      dramDifferentialSenseNominalExtendedRate_continuous.continuousOn.comp
        htrajectoryContinuous fun _point _hpoint => Set.mem_univ _
  have hderivativeEq :
      ∀ᵐ point ∂MeasureTheory.volume.restrict
          (Set.uIcc (0 : ℝ) horizon),
        deriv trajectory point = fieldTrace point := by
    filter_upwards [hbehavior.2.2] with point hpoint
    obtain ⟨derivative, htrajectoryDerivative, hresidual⟩ := hpoint
    rw [htrajectoryDerivative.deriv]
    change derivative =
      dramDifferentialSenseBalancedRate world (trajectory point) at hresidual
    exact hresidual.trans
      (dramDifferentialSense_nominal_extended_rate_eq
        hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap)
  have hderivativeEq' :
      ∀ᵐ point, point ∈ Set.uIcc (0 : ℝ) horizon →
        deriv trajectory point = fieldTrace point :=
    MeasureTheory.ae_imp_of_ae_restrict hderivativeEq
  have htrajectoryEqPrimitive :
      Set.EqOn trajectory primitive (Set.Icc (0 : ℝ) horizon) := by
    intro point hpoint
    have hsubinterval :
        Set.uIcc (0 : ℝ) point ⊆ Set.uIcc (0 : ℝ) horizon := by
      rw [Set.uIcc_of_le hpoint.1, Set.uIcc_of_le hbehavior.1]
      intro target htarget
      exact ⟨htarget.1, htarget.2.trans hpoint.2⟩
    have htrajectoryACSub :
        AbsolutelyContinuousOnInterval trajectory 0 point :=
      hbehavior.2.1.mono hsubinterval
    have hintegrals :
        (∫ t in (0 : ℝ)..point, deriv trajectory t) =
          ∫ t in (0 : ℝ)..point, fieldTrace t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [hderivativeEq'] with target htarget
      intro htargetInterval
      apply htarget
      exact hsubinterval (Set.uIoc_subset_uIcc htargetInterval)
    have hfundamental :=
      htrajectoryACSub.integral_deriv_eq_sub
    dsimp only [primitive]
    rw [← hintegrals, hfundamental]
    ring
  have hfieldTraceIntegrable :
      IntervalIntegrable fieldTrace MeasureTheory.volume 0 time := by
    exact
      (hfieldTraceContinuous.mono
        (Set.uIcc_subset_Icc
          ⟨le_rfl, hbehavior.1⟩ htime)).intervalIntegrable
  letI : Fact (time ∈ Set.Icc (0 : ℝ) horizon) := ⟨htime⟩
  have hintegralDerivative :
      HasDerivWithinAt
        (fun point => ∫ t in (0 : ℝ)..point, fieldTrace t)
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
      hintegralDerivative.const_add (trajectory 0)
  exact hprimitiveDerivative.congr
    (fun point hpoint => htrajectoryEqPrimitive hpoint)
    (htrajectoryEqPrimitive htime)

/-- Interior-point form of
`dramDifferentialSense_nominal_scalar_hasDerivWithinAt`. -/
theorem dramDifferentialSense_nominal_scalar_hasDerivAt
    {world : DramDifferentialSenseWorld}
    {trajectory : DenseTrace ℝ} {horizon time : ℝ}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000)
    (hbehavior :
      dramDifferentialSenseBalancedDAE.ACBehavesOn
        world horizon trajectory)
    (htime0 : 0 < time)
    (htimeHorizon : time < horizon) :
    HasDerivAt trajectory
      (dramDifferentialSenseNominalExtendedRate (trajectory time))
      time :=
  (dramDifferentialSense_nominal_scalar_hasDerivWithinAt
    hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap hbehavior
    ⟨htime0.le, htimeHorizon.le⟩).hasDerivAt
      (Icc_mem_nhds htime0 htimeHorizon)

private theorem lipschitzOnWith_Icc_union
    {f : ℝ → ℝ} {K : NNReal} {a b c : ℝ}
    (hab : a ≤ b) (hbc : b ≤ c)
    (hleft : LipschitzOnWith K f (Set.Icc a b))
    (hright : LipschitzOnWith K f (Set.Icc b c)) :
    LipschitzOnWith K f (Set.Icc a c) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  wlog hxy : x ≤ y generalizing x y with h
  · rw [dist_comm (f x) (f y), dist_comm x y]
    exact h y hy x hx (le_of_not_ge hxy)
  by_cases hyb : y ≤ b
  · exact hleft.dist_le_mul x ⟨hx.1, hxy.trans hyb⟩
      y ⟨hy.1, hyb⟩
  by_cases hbx : b ≤ x
  · exact hright.dist_le_mul x ⟨hbx, hx.2⟩
      y ⟨hbx.trans hxy, hy.2⟩
  have hxb : x ≤ b := le_of_not_ge hbx
  have hby : b ≤ y := le_of_not_ge hyb
  calc
    dist (f x) (f y) ≤ dist (f x) (f b) + dist (f b) (f y) :=
      dist_triangle _ _ _
    _ ≤ K * dist x b + K * dist b y :=
      add_le_add
        (hleft.dist_le_mul x ⟨hx.1, hxb⟩ b ⟨hab, le_rfl⟩)
        (hright.dist_le_mul b ⟨le_rfl, hbc⟩ y ⟨hby, hy.2⟩)
    _ = K * dist x y := by
      simp only [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hxb),
        abs_of_nonpos (sub_nonpos.mpr hby),
        abs_of_nonpos (sub_nonpos.mpr hxy)]
      ring

/-- Conservative Lipschitz constant for the complete five-region source
field on a bounded voltage interval. -/
noncomputable def dramDifferentialSenseNominalExtendedRateLipschitz
    (bound : ℝ) : NNReal :=
  (4000000000 * (|bound| + 1)).toNNReal

set_option maxHeartbeats 1200000 in
/-- The complete source field is Lipschitz on every bounded interval
containing the rail domain. This is the finite-horizon uniqueness certificate:
every absolutely-continuous trajectory has bounded image, so one such
interval covers any pair of candidate trajectories. -/
theorem dramDifferentialSenseNominalExtendedRate_lipschitzOn
    {bound : ℝ} (hbound : 5 / 2 ≤ bound) :
    LipschitzOnWith
      (dramDifferentialSenseNominalExtendedRateLipschitz bound)
      dramDifferentialSenseNominalExtendedRate
      (Set.Icc (-bound) bound) := by
  have hbound0 : 0 ≤ bound := by nlinarith [hbound]
  let negativeOuter : ℝ → ℝ := fun deviation =>
    -(1000000000 / 3) *
      (-3 / 2 * deviation ^ 2 +
        (-7 / 2) * deviation + 5 / 8)
  let negativeMiddle : ℝ → ℝ := fun deviation =>
    -(1000000000 / 3) *
      (-2 * deviation ^ 2 + (-5) * deviation - 1 / 2)
  let center : ℝ → ℝ := fun deviation =>
    1000000000 * deviation
  let positiveMiddle : ℝ → ℝ := fun deviation =>
    (1000000000 / 3) *
      (-2 * deviation ^ 2 + 5 * deviation - 1 / 2)
  let positiveOuter : ℝ → ℝ := fun deviation =>
    (1000000000 / 3) *
      (-3 / 2 * deviation ^ 2 + 7 / 2 * deviation + 5 / 8)
  have hnegativeOuter :
      LipschitzOnWith
        (dramDifferentialSenseNominalExtendedRateLipschitz bound)
        dramDifferentialSenseNominalExtendedRate
        (Set.Icc (-bound) (-(3 / 2))) := by
    have hpoly :
        LipschitzOnWith
          (dramDifferentialSenseNominalExtendedRateLipschitz bound)
          negativeOuter (Set.Icc (-bound) (-(3 / 2))) := by
      apply
        (convex_Icc (-bound) (-(3 / 2)))
          |>.lipschitzOnWith_of_nnnorm_deriv_le
      · intro x hx
        dsimp only [negativeOuter]
        fun_prop
      · intro x hx
        have hsq :
            HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
          simpa using hasDerivAt_pow 2 x
        have hderiv :
            HasDerivAt negativeOuter
              ((1000000000 / 3) * (3 * x + 7 / 2)) x := by
          dsimp only [negativeOuter]
          have hraw :=
            ((((hsq.const_mul (-3 / 2)).add
              ((hasDerivAt_id x).const_mul (-7 / 2)))
              |>.add_const (5 / 8))
              |>.const_mul (-(1000000000 / 3)))
          apply hraw.congr_deriv
          ring
        rw [hderiv.deriv, ← NNReal.coe_le_coe]
        simp only [dramDifferentialSenseNominalExtendedRateLipschitz,
          coe_nnnorm]
        rw [Real.coe_toNNReal _ (by positivity)]
        rw [abs_of_nonneg hbound0]
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> nlinarith [hx.1, hx.2, hbound]
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hxformula :
        dramDifferentialSenseNominalExtendedRate x =
          negativeOuter x := by
      unfold dramDifferentialSenseNominalExtendedRate
      rw [if_pos hx.2]
      dsimp only [negativeOuter]
      ring
    have hyformula :
        dramDifferentialSenseNominalExtendedRate y =
          negativeOuter y := by
      unfold dramDifferentialSenseNominalExtendedRate
      rw [if_pos hy.2]
      dsimp only [negativeOuter]
      ring
    rw [hxformula, hyformula]
    exact hpoly.dist_le_mul x hx y hy
  have hnegativeMiddle :
      LipschitzOnWith
        (dramDifferentialSenseNominalExtendedRateLipschitz bound)
        dramDifferentialSenseNominalExtendedRate
        (Set.Icc (-(3 / 2)) (-(1 / 2))) := by
    have hpoly :
        LipschitzOnWith
          (dramDifferentialSenseNominalExtendedRateLipschitz bound)
          negativeMiddle
          (Set.Icc (-(3 / 2)) (-(1 / 2))) := by
      apply
        (convex_Icc (-(3 / 2)) (-(1 / 2)))
          |>.lipschitzOnWith_of_nnnorm_deriv_le
      · intro x hx
        dsimp only [negativeMiddle]
        fun_prop
      · intro x hx
        have hsq :
            HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
          simpa using hasDerivAt_pow 2 x
        have hderiv :
            HasDerivAt negativeMiddle
              ((1000000000 / 3) * (4 * x + 5)) x := by
          dsimp only [negativeMiddle]
          have hraw :=
            ((((hsq.const_mul (-2)).add
              ((hasDerivAt_id x).const_mul (-5)))
              |>.sub_const (1 / 2))
              |>.const_mul (-(1000000000 / 3)))
          apply hraw.congr_deriv
          ring
        rw [hderiv.deriv, ← NNReal.coe_le_coe]
        simp only [dramDifferentialSenseNominalExtendedRateLipschitz,
          coe_nnnorm]
        rw [Real.coe_toNNReal _ (by positivity)]
        rw [abs_of_nonneg hbound0]
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> nlinarith [hx.1, hx.2, hbound]
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hxformula :
        dramDifferentialSenseNominalExtendedRate x =
          negativeMiddle x := by
      unfold dramDifferentialSenseNominalExtendedRate
      by_cases hleft : x ≤ -(3 / 2)
      · have : x = -(3 / 2) := le_antisymm hleft hx.1
        subst x
        norm_num [negativeMiddle]
      · rw [if_neg hleft, if_pos hx.2]
        dsimp only [negativeMiddle]
        ring
    have hyformula :
        dramDifferentialSenseNominalExtendedRate y =
          negativeMiddle y := by
      unfold dramDifferentialSenseNominalExtendedRate
      by_cases hleft : y ≤ -(3 / 2)
      · have : y = -(3 / 2) := le_antisymm hleft hy.1
        subst y
        norm_num [negativeMiddle]
      · rw [if_neg hleft, if_pos hy.2]
        dsimp only [negativeMiddle]
        ring
    rw [hxformula, hyformula]
    exact hpoly.dist_le_mul x hx y hy
  have hcenter :
      LipschitzOnWith
        (dramDifferentialSenseNominalExtendedRateLipschitz bound)
        dramDifferentialSenseNominalExtendedRate
        (Set.Icc (-(1 / 2)) (1 / 2)) := by
    have hpoly :
        LipschitzOnWith
          (dramDifferentialSenseNominalExtendedRateLipschitz bound)
          center (Set.Icc (-(1 / 2)) (1 / 2)) := by
      apply
        (convex_Icc (-(1 / 2)) (1 / 2))
          |>.lipschitzOnWith_of_nnnorm_deriv_le
      · intro x hx
        dsimp only [center]
        fun_prop
      · intro x hx
        have hderiv :
            HasDerivAt center 1000000000 x := by
          dsimp only [center]
          simpa using
            (hasDerivAt_id x).const_mul (1000000000 : ℝ)
        rw [hderiv.deriv, ← NNReal.coe_le_coe]
        simp only [dramDifferentialSenseNominalExtendedRateLipschitz,
          coe_nnnorm]
        rw [Real.coe_toNNReal _ (by positivity)]
        rw [abs_of_nonneg hbound0]
        norm_num
        nlinarith [hbound]
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hxformula :
        dramDifferentialSenseNominalExtendedRate x = center x := by
      unfold dramDifferentialSenseNominalExtendedRate
      have hnotLeft : ¬x ≤ -(3 / 2) := by nlinarith [hx.1]
      by_cases hmiddle : x ≤ -(1 / 2)
      · have : x = -(1 / 2) := le_antisymm hmiddle hx.1
        subst x
        norm_num [center]
      · rw [if_neg hnotLeft, if_neg hmiddle, if_pos hx.2]
    have hyformula :
        dramDifferentialSenseNominalExtendedRate y = center y := by
      unfold dramDifferentialSenseNominalExtendedRate
      have hnotLeft : ¬y ≤ -(3 / 2) := by nlinarith [hy.1]
      by_cases hmiddle : y ≤ -(1 / 2)
      · have : y = -(1 / 2) := le_antisymm hmiddle hy.1
        subst y
        norm_num [center]
      · rw [if_neg hnotLeft, if_neg hmiddle, if_pos hy.2]
    rw [hxformula, hyformula]
    exact hpoly.dist_le_mul x hx y hy
  have hpositiveMiddle :
      LipschitzOnWith
        (dramDifferentialSenseNominalExtendedRateLipschitz bound)
        dramDifferentialSenseNominalExtendedRate
        (Set.Icc (1 / 2) (3 / 2)) := by
    have hpoly :
        LipschitzOnWith
          (dramDifferentialSenseNominalExtendedRateLipschitz bound)
          positiveMiddle (Set.Icc (1 / 2) (3 / 2)) := by
      apply
        (convex_Icc (1 / 2) (3 / 2))
          |>.lipschitzOnWith_of_nnnorm_deriv_le
      · intro x hx
        dsimp only [positiveMiddle]
        fun_prop
      · intro x hx
        have hsq :
            HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
          simpa using hasDerivAt_pow 2 x
        have hderiv :
            HasDerivAt positiveMiddle
              ((1000000000 / 3) * (-4 * x + 5)) x := by
          dsimp only [positiveMiddle]
          have hraw :=
            ((((hsq.const_mul (-2)).add
              ((hasDerivAt_id x).const_mul 5))
              |>.sub_const (1 / 2))
              |>.const_mul (1000000000 / 3))
          apply hraw.congr_deriv
          ring
        rw [hderiv.deriv, ← NNReal.coe_le_coe]
        simp only [dramDifferentialSenseNominalExtendedRateLipschitz,
          coe_nnnorm]
        rw [Real.coe_toNNReal _ (by positivity)]
        rw [abs_of_nonneg hbound0]
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> nlinarith [hx.1, hx.2, hbound]
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hxformula :
        dramDifferentialSenseNominalExtendedRate x =
          positiveMiddle x := by
      unfold dramDifferentialSenseNominalExtendedRate
      have h1 : ¬x ≤ -(3 / 2) := by nlinarith [hx.1]
      have h2 : ¬x ≤ -(1 / 2) := by nlinarith [hx.1]
      by_cases hcenter : x ≤ 1 / 2
      · have : x = 1 / 2 := le_antisymm hcenter hx.1
        subst x
        norm_num [positiveMiddle]
      · rw [if_neg h1, if_neg h2, if_neg hcenter, if_pos hx.2]
    have hyformula :
        dramDifferentialSenseNominalExtendedRate y =
          positiveMiddle y := by
      unfold dramDifferentialSenseNominalExtendedRate
      have h1 : ¬y ≤ -(3 / 2) := by nlinarith [hy.1]
      have h2 : ¬y ≤ -(1 / 2) := by nlinarith [hy.1]
      by_cases hcenter : y ≤ 1 / 2
      · have : y = 1 / 2 := le_antisymm hcenter hy.1
        subst y
        norm_num [positiveMiddle]
      · rw [if_neg h1, if_neg h2, if_neg hcenter, if_pos hy.2]
    rw [hxformula, hyformula]
    exact hpoly.dist_le_mul x hx y hy
  have hpositiveOuter :
      LipschitzOnWith
        (dramDifferentialSenseNominalExtendedRateLipschitz bound)
        dramDifferentialSenseNominalExtendedRate
        (Set.Icc (3 / 2) bound) := by
    have hpoly :
        LipschitzOnWith
          (dramDifferentialSenseNominalExtendedRateLipschitz bound)
          positiveOuter (Set.Icc (3 / 2) bound) := by
      apply
        (convex_Icc (3 / 2) bound)
          |>.lipschitzOnWith_of_nnnorm_deriv_le
      · intro x hx
        dsimp only [positiveOuter]
        fun_prop
      · intro x hx
        have hsq :
            HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
          simpa using hasDerivAt_pow 2 x
        have hderiv :
            HasDerivAt positiveOuter
              ((1000000000 / 3) * (-3 * x + 7 / 2)) x := by
          dsimp only [positiveOuter]
          have hraw :=
            ((((hsq.const_mul (-3 / 2)).add
              ((hasDerivAt_id x).const_mul (7 / 2)))
              |>.add_const (5 / 8))
              |>.const_mul (1000000000 / 3))
          apply hraw.congr_deriv
          ring
        rw [hderiv.deriv, ← NNReal.coe_le_coe]
        simp only [dramDifferentialSenseNominalExtendedRateLipschitz,
          coe_nnnorm]
        rw [Real.coe_toNNReal _ (by positivity)]
        rw [abs_of_nonneg hbound0]
        rw [Real.norm_eq_abs, abs_le]
        constructor <;> nlinarith [hx.1, hx.2, hbound]
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    have hxformula :
        dramDifferentialSenseNominalExtendedRate x =
          positiveOuter x := by
      unfold dramDifferentialSenseNominalExtendedRate
      have h1 : ¬x ≤ -(3 / 2) := by nlinarith [hx.1]
      have h2 : ¬x ≤ -(1 / 2) := by nlinarith [hx.1]
      have h3 : ¬x ≤ 1 / 2 := by nlinarith [hx.1]
      by_cases hmiddle : x ≤ 3 / 2
      · have : x = 3 / 2 := le_antisymm hmiddle hx.1
        subst x
        norm_num [positiveOuter]
      · rw [if_neg h1, if_neg h2, if_neg h3, if_neg hmiddle]
    have hyformula :
        dramDifferentialSenseNominalExtendedRate y =
          positiveOuter y := by
      unfold dramDifferentialSenseNominalExtendedRate
      have h1 : ¬y ≤ -(3 / 2) := by nlinarith [hy.1]
      have h2 : ¬y ≤ -(1 / 2) := by nlinarith [hy.1]
      have h3 : ¬y ≤ 1 / 2 := by nlinarith [hy.1]
      by_cases hmiddle : y ≤ 3 / 2
      · have : y = 3 / 2 := le_antisymm hmiddle hy.1
        subst y
        norm_num [positiveOuter]
      · rw [if_neg h1, if_neg h2, if_neg h3, if_neg hmiddle]
    rw [hxformula, hyformula]
    exact hpoly.dist_le_mul x hx y hy
  apply lipschitzOnWith_Icc_union (b := 3 / 2)
    (by nlinarith [hbound]) (by nlinarith [hbound])
  · apply lipschitzOnWith_Icc_union (b := 1 / 2)
      (by nlinarith [hbound]) (by norm_num)
    · apply lipschitzOnWith_Icc_union (b := -(1 / 2))
        (by nlinarith [hbound]) (by norm_num)
      · exact lipschitzOnWith_Icc_union
          (by nlinarith [hbound]) (by norm_num)
          hnegativeOuter hnegativeMiddle
      · exact hcenter
    · exact hpositiveMiddle
  · exact hpositiveOuter

private theorem dramDifferentialSenseNominalBalancedRate_lipschitz_region1 :
    LipschitzOnWith (2000000000 : NNReal)
      dramDifferentialSenseNominalBalancedRate
      (Set.Icc (0 : ℝ) (1 / 2)) := by
  have hlinear :
      LipschitzOnWith (2000000000 : NNReal)
        (fun deviation : ℝ => 1000000000 * deviation)
        (Set.Icc (0 : ℝ) (1 / 2)) := by
    apply (convex_Icc (0 : ℝ) (1 / 2))
      |>.lipschitzOnWith_of_nnnorm_deriv_le
    · intro x hx
      fun_prop
    · intro x hx
      have hderiv :
          HasDerivAt (fun y : ℝ => 1000000000 * y) 1000000000 x := by
        exact ((hasDerivAt_id x).const_mul 1000000000).congr_deriv
          (by ring)
      rw [hderiv.deriv, ← NNReal.coe_le_coe]
      norm_num
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hxformula :
      dramDifferentialSenseNominalBalancedRate x = 1000000000 * x := by
    unfold dramDifferentialSenseNominalBalancedRate
    rw [if_pos hx.2]
  have hyformula :
      dramDifferentialSenseNominalBalancedRate y = 1000000000 * y := by
    unfold dramDifferentialSenseNominalBalancedRate
    rw [if_pos hy.2]
  rw [hxformula, hyformula]
  exact hlinear.dist_le_mul x hx y hy

private theorem dramDifferentialSenseNominalBalancedRate_lipschitz_region2 :
    LipschitzOnWith (2000000000 : NNReal)
      dramDifferentialSenseNominalBalancedRate
      (Set.Icc (1 / 2 : ℝ) (3 / 2)) := by
  let middle : ℝ → ℝ := fun deviation =>
    (1000000000 / 3) *
      (-2 * deviation ^ 2 + 5 * deviation - 1 / 2)
  have hmiddle :
      LipschitzOnWith (2000000000 : NNReal) middle
        (Set.Icc (1 / 2 : ℝ) (3 / 2)) := by
    dsimp only [middle]
    apply (convex_Icc (1 / 2 : ℝ) (3 / 2))
      |>.lipschitzOnWith_of_nnnorm_deriv_le
    · intro x hx
      fun_prop
    · intro x hx
      have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      have hderiv :
          HasDerivAt
            (fun deviation : ℝ =>
              (1000000000 / 3) *
                (-2 * deviation ^ 2 + 5 * deviation - 1 / 2))
            ((1000000000 / 3) * (-4 * x + 5)) x :=
        ((((hsq.const_mul (-2)).add
          ((hasDerivAt_id x).const_mul 5)).sub_const (1 / 2))
          |>.const_mul (1000000000 / 3)
          |>.congr_deriv (by ring))
      rw [hderiv.deriv, ← NNReal.coe_le_coe]
      simp only [coe_nnnorm, NNReal.coe_ofNat]
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [hx.1, hx.2]
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hxformula :
      dramDifferentialSenseNominalBalancedRate x = middle x := by
    unfold dramDifferentialSenseNominalBalancedRate
    by_cases hsmall : x ≤ 1 / 2
    · have : x = 1 / 2 := le_antisymm hsmall hx.1
      subst x
      norm_num [middle]
    · rw [if_neg hsmall, if_pos hx.2]
  have hyformula :
      dramDifferentialSenseNominalBalancedRate y = middle y := by
    unfold dramDifferentialSenseNominalBalancedRate
    by_cases hsmall : y ≤ 1 / 2
    · have : y = 1 / 2 := le_antisymm hsmall hy.1
      subst y
      norm_num [middle]
    · rw [if_neg hsmall, if_pos hy.2]
  rw [hxformula, hyformula]
  exact hmiddle.dist_le_mul x hx y hy

private theorem dramDifferentialSenseNominalBalancedRate_lipschitz_region3 :
    LipschitzOnWith (2000000000 : NNReal)
      dramDifferentialSenseNominalBalancedRate
      (Set.Icc (3 / 2 : ℝ) (5 / 2)) := by
  let final : ℝ → ℝ := fun deviation =>
    (1000000000 / 3) *
      (-3 / 2 * deviation ^ 2 + 7 / 2 * deviation + 5 / 8)
  have hfinal :
      LipschitzOnWith (2000000000 : NNReal) final
        (Set.Icc (3 / 2 : ℝ) (5 / 2)) := by
    dsimp only [final]
    apply (convex_Icc (3 / 2 : ℝ) (5 / 2))
      |>.lipschitzOnWith_of_nnnorm_deriv_le
    · intro x hx
      fun_prop
    · intro x hx
      have hsq : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
        simpa using hasDerivAt_pow 2 x
      have hderiv :
          HasDerivAt
            (fun deviation : ℝ =>
              (1000000000 / 3) *
                (-3 / 2 * deviation ^ 2 +
                  7 / 2 * deviation + 5 / 8))
            ((1000000000 / 3) * (-3 * x + 7 / 2)) x :=
        ((((hsq.const_mul (-3 / 2)).add
          ((hasDerivAt_id x).const_mul (7 / 2))).add_const (5 / 8))
          |>.const_mul (1000000000 / 3)
          |>.congr_deriv (by ring))
      rw [hderiv.deriv, ← NNReal.coe_le_coe]
      simp only [coe_nnnorm, NNReal.coe_ofNat]
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> nlinarith [hx.1, hx.2]
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hxformula :
      dramDifferentialSenseNominalBalancedRate x = final x := by
    unfold dramDifferentialSenseNominalBalancedRate
    have hnotSmall : ¬x ≤ 1 / 2 := by nlinarith [hx.1]
    by_cases hmiddle : x ≤ 3 / 2
    · have : x = 3 / 2 := le_antisymm hmiddle hx.1
      subst x
      norm_num [final]
    · rw [if_neg hnotSmall, if_neg hmiddle]
  have hyformula :
      dramDifferentialSenseNominalBalancedRate y = final y := by
    unfold dramDifferentialSenseNominalBalancedRate
    have hnotSmall : ¬y ≤ 1 / 2 := by nlinarith [hy.1]
    by_cases hmiddle : y ≤ 3 / 2
    · have : y = 3 / 2 := le_antisymm hmiddle hy.1
      subst y
      norm_num [final]
    · rw [if_neg hnotSmall, if_neg hmiddle]
  rw [hxformula, hyformula]
  exact hfinal.dist_le_mul x hx y hy

/-- Quantitative regularity of the complete three-region source-derived
field on the closed balanced basin. The bound is intentionally conservative;
its role is to support existence and uniqueness, not characterize gain. -/
theorem dramDifferentialSenseNominalBalancedRate_lipschitzOn :
    LipschitzOnWith (2000000000 : NNReal)
      dramDifferentialSenseNominalBalancedRate
      (Set.Icc (0 : ℝ) (5 / 2)) := by
  apply lipschitzOnWith_Icc_union (b := 3 / 2)
    (by norm_num) (by norm_num)
  · apply lipschitzOnWith_Icc_union (b := 1 / 2)
      (by norm_num) (by norm_num)
    · exact
        dramDifferentialSenseNominalBalancedRate_lipschitz_region1
    · exact
        dramDifferentialSenseNominalBalancedRate_lipschitz_region2
  · exact dramDifferentialSenseNominalBalancedRate_lipschitz_region3

set_option maxHeartbeats 400000 in
/-- The compact closed form above is definitionally tied back to the
primitive MOS1 currents projected from the nominal deck. -/
theorem dramDifferentialSense_nominal_balanced_rate_eq
    {world : DramDifferentialSenseWorld} {deviation : ℝ}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000)
    (hdeviation0 : 0 ≤ deviation)
    (_hdeviationRail : deviation ≤ 5 / 2) :
    dramDifferentialSenseBalancedRate world deviation =
      dramDifferentialSenseNominalBalancedRate deviation := by
  unfold dramDifferentialSenseNominalBalancedRate
  by_cases hsmall : deviation ≤ 1 / 2
  · rw [if_pos hsmall]
    unfold dramDifferentialSenseBalancedRate
      dramDifferentialSenseNCurrent
      dramDifferentialSensePCurrent
      mos1ForwardCurrent
    rw [hsupply, hnThreshold, hpThreshold, hnBeta, hpBeta, hTrueCap]
    norm_num
    split_ifs <;> nlinarith
  · rw [if_neg hsmall]
    by_cases hmiddle : deviation ≤ 3 / 2
    · rw [if_pos hmiddle]
      unfold dramDifferentialSenseBalancedRate
        dramDifferentialSenseNCurrent
        dramDifferentialSensePCurrent
        mos1ForwardCurrent
      rw [hsupply, hnThreshold, hpThreshold, hnBeta, hpBeta, hTrueCap]
      norm_num
      split_ifs <;> nlinarith
    · rw [if_neg hmiddle]
      unfold dramDifferentialSenseBalancedRate
        dramDifferentialSenseNCurrent
        dramDifferentialSensePCurrent
        mos1ForwardCurrent
      rw [hsupply, hnThreshold, hpThreshold, hnBeta, hpBeta, hTrueCap]
      norm_num
      split_ifs <;> nlinarith

/-- Every nonzero balanced differential below the selected rail is
regenerative in the source deck's MOS1 model. This covers the full basin
slice, rather than only the small-signal saturation region around the
metastable point. -/
theorem dramDifferentialSense_nominal_balanced_rate_positive
    {world : DramDifferentialSenseWorld} {deviation : ℝ}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000)
    (hdeviation : 0 < deviation)
    (hdeviationRail : deviation < 5 / 2) :
    0 < dramDifferentialSenseBalancedRate world deviation := by
  rw [dramDifferentialSense_nominal_balanced_rate_eq
    hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
    (le_of_lt hdeviation) (le_of_lt hdeviationRail)]
  unfold dramDifferentialSenseNominalBalancedRate
  split_ifs <;> nlinarith

@[simp]
theorem dramDifferentialSense_nominal_balanced_rate_zero :
    dramDifferentialSenseNominalBalancedRate 0 = 0 := by
  norm_num [dramDifferentialSenseNominalBalancedRate]

@[simp]
theorem dramDifferentialSense_nominal_balanced_rate_rail :
    dramDifferentialSenseNominalBalancedRate (5 / 2) = 0 := by
  norm_num [dramDifferentialSenseNominalBalancedRate]

/-- The reduced vector field points toward increasing differential
throughout the closed midpoint-to-selected-rail interval and is tangent at
the two equilibria. -/
theorem dramDifferentialSense_nominal_balanced_rate_nonnegative
    {deviation : ℝ}
    (hdeviation0 : 0 ≤ deviation)
    (hdeviationRail : deviation ≤ 5 / 2) :
    0 ≤ dramDifferentialSenseNominalBalancedRate deviation := by
  unfold dramDifferentialSenseNominalBalancedRate
  by_cases hsmall : deviation ≤ 1 / 2
  · rw [if_pos hsmall]
    positivity
  · rw [if_neg hsmall]
    by_cases hmiddle : deviation ≤ 3 / 2
    · rw [if_pos hmiddle]
      have hleft : 0 ≤ 2 * deviation - 1 := by linarith
      have hright : 0 ≤ 2 - deviation := by linarith
      have hproduct :
          0 ≤ (2 * deviation - 1) * (2 - deviation) :=
        mul_nonneg hleft hright
      norm_num
      nlinarith
    · rw [if_neg hmiddle]
      have hleft : 0 ≤ 5 / 2 - deviation := by linarith
      have hright : 0 ≤ 3 / 2 * deviation + 1 / 4 := by
        linarith
      have hproduct :
          0 ≤ (5 / 2 - deviation) *
            (3 / 2 * deviation + 1 / 4) :=
        mul_nonneg hleft hright
      norm_num
      nlinarith

/-- Source-backed form of the closed-interval vector-field bound. -/
theorem dramDifferentialSense_nominal_balanced_rate_nonnegative_of_source
    {world : DramDifferentialSenseWorld} {deviation : ℝ}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000)
    (hdeviation0 : 0 ≤ deviation)
    (hdeviationRail : deviation ≤ 5 / 2) :
    0 ≤ dramDifferentialSenseBalancedRate world deviation := by
  rw [dramDifferentialSense_nominal_balanced_rate_eq
    hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
    hdeviation0 hdeviationRail]
  exact dramDifferentialSense_nominal_balanced_rate_nonnegative
    hdeviation0 hdeviationRail

/-! ## Finite-horizon construction across all MOS regions

The clamped field below is an internal proof device. It agrees with the
source-derived field on the physical rail domain and is frozen at the two
equilibria outside it. Picard-Lindelöf constructs a trajectory for this
globally Lipschitz extension; the subsequent barrier proof establishes that
the witness never uses the extension outside the physical domain. -/

private noncomputable def dramDifferentialSenseNominalClampedRate
    (deviation : ℝ) : ℝ :=
  dramDifferentialSenseNominalBalancedRate
    (Set.projIcc (0 : ℝ) (5 / 2) (by norm_num) deviation)

private theorem dramDifferentialSenseNominalClampedRate_lipschitz :
    LipschitzWith (2000000000 : NNReal)
      dramDifferentialSenseNominalClampedRate := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  let px := Set.projIcc (0 : ℝ) (5 / 2) (by norm_num) x
  let py := Set.projIcc (0 : ℝ) (5 / 2) (by norm_num) y
  change dist
      (dramDifferentialSenseNominalBalancedRate px)
      (dramDifferentialSenseNominalBalancedRate py) ≤
    (2000000000 : ℝ) * dist x y
  calc
    dist
        (dramDifferentialSenseNominalBalancedRate px)
        (dramDifferentialSenseNominalBalancedRate py) ≤
      (2000000000 : ℝ) * dist px py :=
        dramDifferentialSenseNominalBalancedRate_lipschitzOn
          |>.dist_le_mul px px.property py py.property
    _ ≤ (2000000000 : ℝ) * dist x y := by
      gcongr
      simpa [px, py] using
        ((LipschitzWith.projIcc
          (show (0 : ℝ) ≤ 5 / 2 by norm_num)).dist_le_mul x y)

private theorem dramDifferentialSenseNominalClampedRate_norm_le
    (x : ℝ) :
    ‖dramDifferentialSenseNominalClampedRate x‖ ≤ 5000000000 := by
  let px := Set.projIcc (0 : ℝ) (5 / 2) (by norm_num) x
  calc
    ‖dramDifferentialSenseNominalClampedRate x‖ =
        dist
          (dramDifferentialSenseNominalBalancedRate px)
          (dramDifferentialSenseNominalBalancedRate 0) := by
      simp [dramDifferentialSenseNominalClampedRate, px]
    _ ≤ (2000000000 : ℝ) * dist (px : ℝ) 0 :=
      dramDifferentialSenseNominalBalancedRate_lipschitzOn
        |>.dist_le_mul (px : ℝ) px.property 0 (by norm_num)
    _ ≤ 5000000000 := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg px.property.1]
      nlinarith [px.property.2]

private theorem dramDifferentialSenseNominalClampedRate_nonnegative
    (x : ℝ) :
    0 ≤ dramDifferentialSenseNominalClampedRate x := by
  unfold dramDifferentialSenseNominalClampedRate
  exact dramDifferentialSense_nominal_balanced_rate_nonnegative
    (Set.projIcc (0 : ℝ) (5 / 2) (by norm_num) x).property.1
    (Set.projIcc (0 : ℝ) (5 / 2) (by norm_num) x).property.2

private theorem dramDifferentialSenseNominalClampedRate_eq_zero_of_rail_le
    {x : ℝ} (hx : 5 / 2 ≤ x) :
    dramDifferentialSenseNominalClampedRate x = 0 := by
  unfold dramDifferentialSenseNominalClampedRate
  rw [Set.projIcc_of_right_le
    (by norm_num : (0 : ℝ) ≤ 5 / 2) hx]
  exact dramDifferentialSense_nominal_balanced_rate_rail

private theorem dramDifferentialSenseNominalClampedRate_eq_of_mem
    {deviation : ℝ}
    (hdeviation : deviation ∈ Set.Icc (0 : ℝ) (5 / 2)) :
    dramDifferentialSenseNominalClampedRate deviation =
      dramDifferentialSenseNominalBalancedRate deviation := by
  unfold dramDifferentialSenseNominalClampedRate
  rw [Set.projIcc_of_mem (by norm_num) hdeviation]

private theorem dramDifferentialSense_exists_clamped_solution
    {initialDeviation horizon : ℝ}
    (hhorizon : 0 ≤ horizon) :
    ∃ trajectory : ℝ → ℝ,
      trajectory 0 = initialDeviation ∧
      ∀ time ∈ Set.Icc (0 : ℝ) horizon,
        HasDerivWithinAt trajectory
          (dramDifferentialSenseNominalClampedRate (trajectory time))
          (Set.Icc (0 : ℝ) horizon) time := by
  let horizonNN : NNReal := ⟨horizon, hhorizon⟩
  let radius : NNReal := 5000000000 * horizonNN
  let initialTime : Set.Icc (0 : ℝ) horizon :=
    ⟨0, le_rfl, hhorizon⟩
  have hpl :
      IsPicardLindelof
        (fun _time : ℝ =>
          dramDifferentialSenseNominalClampedRate)
        initialTime initialDeviation radius 0
        5000000000 2000000000 := by
    apply IsPicardLindelof.of_time_independent
    · intro x hx
      exact dramDifferentialSenseNominalClampedRate_norm_le x
    · exact
        dramDifferentialSenseNominalClampedRate_lipschitz
          |>.lipschitzOnWith
    · dsimp [radius, horizonNN, initialTime]
      simp only [sub_zero, max_eq_left hhorizon]
      exact le_rfl
  simpa [initialTime] using
    hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

private theorem dramDifferentialSense_clamped_solution_invariant
    {trajectory : ℝ → ℝ} {initialDeviation horizon : ℝ}
    (hhorizon : 0 ≤ horizon)
    (hinitial : trajectory 0 = initialDeviation)
    (hinitial0 : 0 ≤ initialDeviation)
    (hinitialRail : initialDeviation ≤ 5 / 2)
    (hsolution :
      ∀ time ∈ Set.Icc (0 : ℝ) horizon,
        HasDerivWithinAt trajectory
          (dramDifferentialSenseNominalClampedRate (trajectory time))
          (Set.Icc (0 : ℝ) horizon) time) :
    ∀ time ∈ Set.Icc (0 : ℝ) horizon,
      0 ≤ trajectory time ∧ trajectory time ≤ 5 / 2 := by
  have hcontinuous :
      ContinuousOn trajectory (Set.Icc (0 : ℝ) horizon) := by
    intro time htime
    exact (hsolution time htime).continuousWithinAt
  have hmonotone :
      MonotoneOn trajectory (Set.Icc (0 : ℝ) horizon) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg
      (convex_Icc (0 : ℝ) horizon) hcontinuous
    · intro time htime
      exact (hsolution time (interior_subset htime)).mono
        interior_subset
    · intro time htime
      exact
        dramDifferentialSenseNominalClampedRate_nonnegative _
  intro time htime
  constructor
  · have hfromInitial :
        trajectory 0 ≤ trajectory time :=
      hmonotone ⟨le_rfl, hhorizon⟩ htime htime.1
    rw [hinitial] at hfromInitial
    exact hinitial0.trans hfromInitial
  · apply le_of_forall_pos_le_add
    intro epsilon hepsilon
    let slope : ℝ := epsilon / (horizon + 1)
    have hslope : 0 < slope := by
      dsimp [slope]
      exact div_pos hepsilon (by linarith)
    have hrightDerivative :
        ∀ point ∈ Set.Ico (0 : ℝ) horizon,
          HasDerivWithinAt trajectory
            (dramDifferentialSenseNominalClampedRate
              (trajectory point))
            (Set.Ici point) point := by
      intro point hpoint
      exact
        ((hsolution point ⟨hpoint.1, hpoint.2.le⟩)
          |>.mono_of_mem_nhdsWithin
            (Icc_mem_nhdsGT_of_mem hpoint)).Ici_of_Ioi
    have hbarrier :
        ∀ ⦃point⦄, point ∈ Set.Icc (0 : ℝ) horizon →
          trajectory point ≤ 5 / 2 + slope * point := by
      refine image_le_of_deriv_right_lt_deriv_boundary
        (f := trajectory)
        (f' := fun point =>
          dramDifferentialSenseNominalClampedRate
            (trajectory point))
        (B := fun point => 5 / 2 + slope * point)
        (B' := fun _point => slope)
        hcontinuous hrightDerivative ?_ ?_ ?_
      · rw [hinitial]
        simpa using hinitialRail
      · intro point
        exact
          (((hasDerivAt_id point).const_mul slope).const_add (5 / 2))
            |>.congr_deriv (by ring)
      · intro point hpoint heq
        have hrail : 5 / 2 ≤ trajectory point := by
          rw [heq]
          exact le_add_of_nonneg_right
            (mul_nonneg hslope.le hpoint.1)
        rw [
          dramDifferentialSenseNominalClampedRate_eq_zero_of_rail_le
            hrail]
        exact hslope
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

/-- For every finite horizon and every initial balanced differential between
the metastable midpoint and the selected rail, there exists an
absolutely-continuous solution of the complete source-derived scalar DAE. The
same witness is proved to remain in the MOS model's rail domain. -/
theorem dramDifferentialSense_nominal_scalar_realizable
    {world : DramDifferentialSenseWorld}
    {initialDeviation horizon : ℝ}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000)
    (hinitial0 : 0 ≤ initialDeviation)
    (hinitialRail : initialDeviation ≤ 5 / 2)
    (hhorizon : 0 ≤ horizon) :
    ∃ trajectory : DenseTrace ℝ,
      trajectory 0 = initialDeviation ∧
      dramDifferentialSenseBalancedDAE.ACBehavesOn
        world horizon trajectory ∧
      ∀ time, 0 ≤ time → time ≤ horizon →
        0 ≤ trajectory time ∧ trajectory time ≤ 5 / 2 := by
  obtain ⟨trajectory, hinitial, hsolution⟩ :=
    dramDifferentialSense_exists_clamped_solution
      (initialDeviation := initialDeviation) hhorizon
  have hinvariant :
      ∀ time ∈ Set.Icc (0 : ℝ) horizon,
        0 ≤ trajectory time ∧ trajectory time ≤ 5 / 2 :=
    dramDifferentialSense_clamped_solution_invariant
      hhorizon hinitial hinitial0 hinitialRail hsolution
  have htrajectoryLipschitz :
      LipschitzOnWith (5000000000 : NNReal)
        trajectory (Set.Icc (0 : ℝ) horizon) := by
    apply
      (convex_Icc (0 : ℝ) horizon)
        |>.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
          hsolution
    intro time htime
    rw [← NNReal.coe_le_coe]
    simpa only [coe_nnnorm, NNReal.coe_ofNat] using
      dramDifferentialSenseNominalClampedRate_norm_le
        (trajectory time)
  have habsolutelyContinuous :
      AbsolutelyContinuousOnInterval trajectory 0 horizon := by
    rw [← Set.uIcc_of_le hhorizon] at htrajectoryLipschitz
    exact htrajectoryLipschitz.absolutelyContinuousOnInterval
  refine ⟨trajectory, hinitial, ⟨hhorizon,
    habsolutelyContinuous, ?_⟩, ?_⟩
  · rw [Set.uIcc_of_le hhorizon,
      ← MeasureTheory.restrict_Ioo_eq_restrict_Icc]
    apply MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioo
    intro time htime
    have hderivative :
        HasDerivAt trajectory
          (dramDifferentialSenseNominalClampedRate
            (trajectory time)) time :=
      (hsolution time ⟨htime.1.le, htime.2.le⟩).hasDerivAt
        (Icc_mem_nhds htime.1 htime.2)
    refine
      ⟨dramDifferentialSenseNominalClampedRate
        (trajectory time), hderivative, ?_⟩
    unfold dramDifferentialSenseBalancedDAE
    have hdomain :=
      hinvariant time ⟨htime.1.le, htime.2.le⟩
    rw [
      dramDifferentialSenseNominalClampedRate_eq_of_mem hdomain]
    exact (dramDifferentialSense_nominal_balanced_rate_eq
      hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
      hdomain.1 hdomain.2).symm
  · intro time htime0 htimeHorizon
    exact hinvariant time ⟨htime0, htimeHorizon⟩

/-- Any two physical scalar trajectories in the closed balanced basin with
the same initial differential coincide. This is the determinacy companion to
`dramDifferentialSense_nominal_scalar_realizable`.

The physical semantics only supplies derivatives almost everywhere, so the
proof does not strengthen the trajectories to smooth ODE solutions. Instead,
it applies an energy argument to the squared trajectory difference. The
source-derived Lipschitz bound makes the exponentially weighted difference
nonincreasing almost everywhere; absolute continuity then integrates that
fact over every requested subinterval. -/
theorem dramDifferentialSense_nominal_scalar_determinate_on_domain
    {world : DramDifferentialSenseWorld}
    {first second : DenseTrace ℝ}
    {horizon time : ℝ}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000)
    (hfirst :
      dramDifferentialSenseBalancedDAE.ACBehavesOn
        world horizon first)
    (hsecond :
      dramDifferentialSenseBalancedDAE.ACBehavesOn
        world horizon second)
    (hinitial : first 0 = second 0)
    (hfirstDomain :
      ∀ point, 0 ≤ point → point ≤ horizon →
        0 ≤ first point ∧ first point ≤ 5 / 2)
    (hsecondDomain :
      ∀ point, 0 ≤ point → point ≤ horizon →
        0 ≤ second point ∧ second point ≤ 5 / 2)
    (htime0 : 0 ≤ time)
    (htimeHorizon : time ≤ horizon) :
    first time = second time := by
  let difference : ℝ → ℝ := first - second
  let energy : ℝ → ℝ := difference * difference
  let weight : ℝ → ℝ :=
    Real.exp ∘ HMul.hMul (-4000000000)
  let weightedEnergy : ℝ → ℝ := weight * energy
  have hdifferenceAC :
      AbsolutelyContinuousOnInterval difference 0 horizon :=
    hfirst.2.1.sub hsecond.2.1
  have henergyAC :
      AbsolutelyContinuousOnInterval energy 0 horizon :=
    hdifferenceAC.mul hdifferenceAC
  have hweightAC :
      AbsolutelyContinuousOnInterval weight 0 horizon := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    exact
      (Real.contDiff_exp.comp
        (contDiff_const.mul contDiff_id)).contDiffOn
  have hweightedEnergyAC :
      AbsolutelyContinuousOnInterval weightedEnergy 0 horizon :=
    hweightAC.mul henergyAC
  have hweightedEnergyDerivative :
      ∀ᵐ point ∂MeasureTheory.volume.restrict
          (Set.uIcc (0 : ℝ) horizon),
        HasDerivAt weightedEnergy
            (weight point *
              (-4000000000 * energy point +
                2 * difference point *
                  (dramDifferentialSenseNominalBalancedRate
                      (first point) -
                    dramDifferentialSenseNominalBalancedRate
                      (second point))))
          point ∧
        deriv weightedEnergy point ≤ 0 := by
    filter_upwards [hfirst.2.2, hsecond.2.2,
      MeasureTheory.ae_restrict_mem measurableSet_uIcc]
      with point hfirstPoint hsecondPoint hpointDomain
    obtain ⟨firstDerivative, hfirstDerivative, hfirstResidual⟩ :=
      hfirstPoint
    obtain ⟨secondDerivative, hsecondDerivative, hsecondResidual⟩ :=
      hsecondPoint
    rw [Set.uIcc_of_le hfirst.1] at hpointDomain
    have hfirstValue :=
      hfirstDomain point hpointDomain.1 hpointDomain.2
    have hsecondValue :=
      hsecondDomain point hpointDomain.1 hpointDomain.2
    have hfirstField :
        firstDerivative =
          dramDifferentialSenseNominalBalancedRate
            (first point) := by
      change firstDerivative =
        dramDifferentialSenseBalancedRate world (first point) at hfirstResidual
      exact hfirstResidual.trans
        (dramDifferentialSense_nominal_balanced_rate_eq
          hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
          hfirstValue.1 hfirstValue.2)
    have hsecondField :
        secondDerivative =
          dramDifferentialSenseNominalBalancedRate
            (second point) := by
      change secondDerivative =
        dramDifferentialSenseBalancedRate world (second point) at hsecondResidual
      exact hsecondResidual.trans
        (dramDifferentialSense_nominal_balanced_rate_eq
          hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
          hsecondValue.1 hsecondValue.2)
    have hfieldDistance :=
      dramDifferentialSenseNominalBalancedRate_lipschitzOn.dist_le_mul
        (first point) hfirstValue (second point) hsecondValue
    rw [Real.dist_eq, Real.dist_eq] at hfieldDistance
    have hproduct :
        difference point *
            (dramDifferentialSenseNominalBalancedRate (first point) -
              dramDifferentialSenseNominalBalancedRate (second point)) ≤
          2000000000 * energy point := by
      calc
        difference point *
              (dramDifferentialSenseNominalBalancedRate (first point) -
                dramDifferentialSenseNominalBalancedRate (second point)) ≤
            |difference point *
              (dramDifferentialSenseNominalBalancedRate (first point) -
                dramDifferentialSenseNominalBalancedRate
                  (second point))| :=
          le_abs_self _
        _ =
            |difference point| *
              |dramDifferentialSenseNominalBalancedRate (first point) -
                dramDifferentialSenseNominalBalancedRate
                  (second point)| := abs_mul _ _
        _ ≤
            |difference point| *
              (2000000000 * |difference point|) := by
          apply mul_le_mul_of_nonneg_left
          · simpa [difference] using hfieldDistance
          · exact abs_nonneg _
        _ = 2000000000 * energy point := by
          have habsSquare :
              |difference point| * |difference point| =
                difference point * difference point := by
            nlinarith [sq_abs (difference point)]
          simp only [energy, Pi.mul_apply]
          calc
            |difference point| *
                (2000000000 * |difference point|) =
              2000000000 *
                (|difference point| * |difference point|) := by ring
            _ = 2000000000 *
                (difference point * difference point) := by
              rw [habsSquare]
    have hdifferenceDerivative :
        HasDerivAt difference
          (dramDifferentialSenseNominalBalancedRate (first point) -
            dramDifferentialSenseNominalBalancedRate (second point))
          point := by
      simpa [hfirstField, hsecondField] using
        hfirstDerivative.sub hsecondDerivative
    have henergyDerivative :
        HasDerivAt energy
          (2 * difference point *
            (dramDifferentialSenseNominalBalancedRate (first point) -
              dramDifferentialSenseNominalBalancedRate (second point)))
          point := by
      have hproductDerivative :=
        hdifferenceDerivative.mul hdifferenceDerivative
      apply hproductDerivative.congr_deriv
      ring
    have hinner :
        HasDerivAt (fun x : ℝ => -4000000000 * x)
          (-4000000000) point := by
      simpa only [id_eq, mul_one] using
        (hasDerivAt_id point).const_mul (-4000000000)
    have hweightDerivative :
        HasDerivAt weight
          (weight point * (-4000000000)) point := by
      have hexponential :=
        (Real.hasDerivAt_exp (-4000000000 * point)).comp
          point hinner
      apply hexponential.congr_deriv
      rfl
    have hderivative :
        HasDerivAt weightedEnergy
            (weight point *
              (-4000000000 * energy point +
                2 * difference point *
                  (dramDifferentialSenseNominalBalancedRate
                      (first point) -
                    dramDifferentialSenseNominalBalancedRate
                      (second point))))
          point := by
      have hmul := hweightDerivative.mul henergyDerivative
      apply hmul.congr_deriv
      ring
    refine ⟨hderivative, ?_⟩
    rw [hderivative.deriv]
    have hweightPositive : 0 < weight point := by
      exact Real.exp_pos _
    apply mul_nonpos_of_nonneg_of_nonpos hweightPositive.le
    linarith
  have hsubinterval :
      Set.uIcc (0 : ℝ) time ⊆ Set.uIcc (0 : ℝ) horizon := by
    rw [Set.uIcc_of_le htime0, Set.uIcc_of_le hfirst.1]
    intro point hpoint
    exact ⟨hpoint.1, hpoint.2.trans htimeHorizon⟩
  have hweightedEnergyACSub :
      AbsolutelyContinuousOnInterval weightedEnergy 0 time :=
    hweightedEnergyAC.mono hsubinterval
  have hweightedEnergyDerivativeSub :
      ∀ᵐ point ∂MeasureTheory.volume.restrict
          (Set.uIcc (0 : ℝ) time),
        deriv weightedEnergy point ≤ 0 := by
    have hderivative :
        ∀ᵐ point ∂MeasureTheory.volume.restrict
            (Set.uIcc (0 : ℝ) horizon),
          deriv weightedEnergy point ≤ 0 :=
      hweightedEnergyDerivative.mono fun _point hpoint => hpoint.2
    exact MeasureTheory.ae_restrict_of_ae_restrict_of_subset
      hsubinterval hderivative
  have hintegral :
      (∫ point in (0 : ℝ)..time, deriv weightedEnergy point) ≤ 0 := by
    have hzero :
        IntervalIntegrable (fun _point : ℝ => (0 : ℝ))
          MeasureTheory.volume 0 time :=
      intervalIntegrable_const
    rw [Set.uIcc_of_le htime0] at hweightedEnergyDerivativeSub
    simpa using
      intervalIntegral.integral_mono_ae_restrict htime0
        hweightedEnergyACSub.intervalIntegrable_deriv hzero
        hweightedEnergyDerivativeSub
  rw [hweightedEnergyACSub.integral_deriv_eq_sub] at hintegral
  have hinitialDifference : difference 0 = 0 := by
    dsimp [difference]
    linarith
  have hweightedEnergyNonnegative : 0 ≤ weightedEnergy time := by
    exact mul_nonneg (Real.exp_pos _).le (mul_self_nonneg _)
  have hweightedEnergyZero : weightedEnergy time = 0 := by
    have hinitialEnergy : weightedEnergy 0 = 0 := by
      simp [weightedEnergy, weight, energy, hinitialDifference]
    rw [hinitialEnergy] at hintegral
    linarith
  have henergyZero : energy time = 0 := by
    have hweightNe : weight time ≠ 0 := (Real.exp_pos _).ne'
    exact (mul_eq_zero.mp hweightedEnergyZero).resolve_left hweightNe
  have hdifferenceZero : difference time = 0 := by
    exact mul_self_eq_zero.mp henergyZero
  dsimp [difference] at hdifferenceZero
  linarith

/-- Any two nominal physical scalar trajectories with the same initial
differential coincide on their complete finite horizon.

No rail-domain premise is assumed. Absolute continuity first bounds both
candidate images on the compact horizon. The complete five-region MOS field
is Lipschitz on an interval containing those images, and Grönwall uniqueness
then applies to the source-derived pointwise ODE capability. -/
theorem dramDifferentialSense_nominal_scalar_determinate
    {world : DramDifferentialSenseWorld}
    {first second : DenseTrace ℝ}
    {horizon time : ℝ}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000)
    (hfirst :
      dramDifferentialSenseBalancedDAE.ACBehavesOn
        world horizon first)
    (hsecond :
      dramDifferentialSenseBalancedDAE.ACBehavesOn
        world horizon second)
    (hinitial : first 0 = second 0)
    (htime0 : 0 ≤ time)
    (htimeHorizon : time ≤ horizon) :
    first time = second time := by
  obtain ⟨firstBound, hfirstBound⟩ :=
    hfirst.2.1.exists_bound
  obtain ⟨secondBound, hsecondBound⟩ :=
    hsecond.2.1.exists_bound
  let bound : ℝ :=
    max (5 / 2) (max firstBound secondBound)
  have hboundRail : 5 / 2 ≤ bound := by
    exact le_max_left _ _
  have hfirstBoundLe : firstBound ≤ bound := by
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hsecondBoundLe : secondBound ≤ bound := by
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hfirstMem :
      ∀ point ∈ Set.Icc (0 : ℝ) horizon,
        first point ∈ Set.Icc (-bound) bound := by
    intro point hpoint
    have hnorm : ‖first point‖ ≤ firstBound := by
      apply hfirstBound point
      rwa [Set.uIcc_of_le hfirst.1]
    have habs : |first point| ≤ bound := by
      rw [← Real.norm_eq_abs]
      exact hnorm.trans hfirstBoundLe
    exact abs_le.mp habs
  have hsecondMem :
      ∀ point ∈ Set.Icc (0 : ℝ) horizon,
        second point ∈ Set.Icc (-bound) bound := by
    intro point hpoint
    have hnorm : ‖second point‖ ≤ secondBound := by
      apply hsecondBound point
      rwa [Set.uIcc_of_le hsecond.1]
    have habs : |second point| ≤ bound := by
      rw [← Real.norm_eq_abs]
      exact hnorm.trans hsecondBoundLe
    exact abs_le.mp habs
  have hfieldLipschitz :=
    dramDifferentialSenseNominalExtendedRate_lipschitzOn
      hboundRail
  have hfirstContinuous :
      ContinuousOn first (Set.Icc (0 : ℝ) horizon) := by
    have hcontinuous := hfirst.2.1.continuousOn
    rwa [Set.uIcc_of_le hfirst.1] at hcontinuous
  have hsecondContinuous :
      ContinuousOn second (Set.Icc (0 : ℝ) horizon) := by
    have hcontinuous := hsecond.2.1.continuousOn
    rwa [Set.uIcc_of_le hsecond.1] at hcontinuous
  have hfirstDerivative :
      ∀ point ∈ Set.Ico (0 : ℝ) horizon,
        HasDerivWithinAt first
          (dramDifferentialSenseNominalExtendedRate
            (first point))
          (Set.Ici point) point := by
    intro point hpoint
    exact
      ((dramDifferentialSense_nominal_scalar_hasDerivWithinAt
          hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
          hfirst ⟨hpoint.1, hpoint.2.le⟩)
        |>.mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGT_of_mem hpoint)).Ici_of_Ioi
  have hsecondDerivative :
      ∀ point ∈ Set.Ico (0 : ℝ) horizon,
        HasDerivWithinAt second
          (dramDifferentialSenseNominalExtendedRate
            (second point))
          (Set.Ici point) point := by
    intro point hpoint
    exact
      ((dramDifferentialSense_nominal_scalar_hasDerivWithinAt
          hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
          hsecond ⟨hpoint.1, hpoint.2.le⟩)
        |>.mono_of_mem_nhdsWithin
          (Icc_mem_nhdsGT_of_mem hpoint)).Ici_of_Ioi
  have hequal :
      Set.EqOn first second (Set.Icc (0 : ℝ) horizon) := by
    apply ODE_solution_unique_of_mem_Icc_right
      (v := fun _point value =>
        dramDifferentialSenseNominalExtendedRate value)
      (s := fun _point => Set.Icc (-bound) bound)
      (K :=
        dramDifferentialSenseNominalExtendedRateLipschitz bound)
    · intro _point _hpoint
      exact hfieldLipschitz
    · exact hfirstContinuous
    · exact hfirstDerivative
    · intro point hpoint
      exact hfirstMem point ⟨hpoint.1, hpoint.2.le⟩
    · exact hsecondContinuous
    · exact hsecondDerivative
    · intro point hpoint
      exact hsecondMem point ⟨hpoint.1, hpoint.2.le⟩
    · exact hinitial
  exact hequal ⟨htime0, htimeHorizon⟩

/-- Every nominal physical scalar trajectory starting in the selected
balanced basin stays there for the complete finite horizon. This is an
all-behavior safety theorem, not a property embedded in the DAE relation:
realizability supplies one invariant witness and source-level determinacy
forces every other candidate trajectory to equal it. -/
theorem dramDifferentialSense_nominal_scalar_invariant
    {world : DramDifferentialSenseWorld}
    {trajectory : DenseTrace ℝ}
    {initialDeviation horizon : ℝ}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000)
    (hbehavior :
      dramDifferentialSenseBalancedDAE.ACBehavesOn
        world horizon trajectory)
    (hinitial : trajectory 0 = initialDeviation)
    (hinitial0 : 0 ≤ initialDeviation)
    (hinitialRail : initialDeviation ≤ 5 / 2) :
    ∀ time, 0 ≤ time → time ≤ horizon →
      0 ≤ trajectory time ∧ trajectory time ≤ 5 / 2 := by
  obtain ⟨witness, hwitnessInitial, hwitnessBehavior,
      hwitnessInvariant⟩ :=
    dramDifferentialSense_nominal_scalar_realizable
      hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
      hinitial0 hinitialRail hbehavior.1
  intro time htime0 htimeHorizon
  have hequal :
      trajectory time = witness time :=
    dramDifferentialSense_nominal_scalar_determinate
      hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
      hbehavior hwitnessBehavior
      (hinitial.trans hwitnessInitial.symm)
      htime0 htimeHorizon
  rw [hequal]
  exact hwitnessInvariant time htime0 htimeHorizon

/-- The complete five-region nominal source field points toward the selected
rail throughout the closed balanced basin. -/
theorem dramDifferentialSenseNominalExtendedRate_nonnegative
    {deviation : ℝ}
    (hdeviation0 : 0 ≤ deviation)
    (hdeviationRail : deviation ≤ 5 / 2) :
    0 ≤ dramDifferentialSenseNominalExtendedRate deviation := by
  unfold dramDifferentialSenseNominalExtendedRate
  split_ifs <;>
    nlinarith [sq_nonneg (deviation - 5 / 2)]

/-- Every nominal physical scalar trajectory in the selected balanced basin
regenerates monotonically toward the selected rail. The basin premise is only
on the initial value; invariance and the derivative sign are both derived
from the source-backed DAE. -/
theorem dramDifferentialSense_nominal_scalar_monotone
    {world : DramDifferentialSenseWorld}
    {trajectory : DenseTrace ℝ}
    {initialDeviation horizon : ℝ}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000)
    (hbehavior :
      dramDifferentialSenseBalancedDAE.ACBehavesOn
        world horizon trajectory)
    (hinitial : trajectory 0 = initialDeviation)
    (hinitial0 : 0 ≤ initialDeviation)
    (hinitialRail : initialDeviation ≤ 5 / 2) :
    MonotoneOn trajectory (Set.Icc (0 : ℝ) horizon) := by
  have hinvariant :=
    dramDifferentialSense_nominal_scalar_invariant
      hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
      hbehavior hinitial hinitial0 hinitialRail
  have hcontinuous :
      ContinuousOn trajectory (Set.Icc (0 : ℝ) horizon) := by
    have hcontinuous := hbehavior.2.1.continuousOn
    rwa [Set.uIcc_of_le hbehavior.1] at hcontinuous
  apply monotoneOn_of_hasDerivWithinAt_nonneg
    (convex_Icc (0 : ℝ) horizon) hcontinuous
  · intro time htime
    exact
      (dramDifferentialSense_nominal_scalar_hasDerivWithinAt
        hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
        hbehavior (interior_subset htime)).mono interior_subset
  · intro time htime
    have hdomain :=
      hinvariant time (interior_subset htime).1
        (interior_subset htime).2
    exact
      dramDifferentialSenseNominalExtendedRate_nonnegative
        hdomain.1 hdomain.2

/-- Any two rail-valid trajectories of the primitive nominal two-node DAE
with the same balanced initial state coincide. The proof first derives
balanced-manifold preservation from KCL, projects both trajectories into the
exact scalar view, and then applies scalar determinacy. -/
theorem dramDifferentialSense_nominal_vector_determinate_on_domain
    {world : DramDifferentialSenseWorld}
    {first second : VectorTrace DramDifferentialSenseIndex}
    {horizon time : ℝ}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000)
    (hComplementCap :
      world.fabricated.complementCapacitance =
        3 / 10000000000000)
    (hfirst :
      dramDifferentialSenseDAE.ACBehavesOn world horizon first)
    (hsecond :
      dramDifferentialSenseDAE.ACBehavesOn world horizon second)
    (hfirstDomain :
      ∀ point, 0 ≤ point → point ≤ horizon →
        DramDifferentialSenseStateInRailDomain world (first point))
    (hsecondDomain :
      ∀ point, 0 ≤ point → point ≤ horizon →
        DramDifferentialSenseStateInRailDomain world (second point))
    (hinitial : first 0 = second 0)
    (hinitialBalanced :
      first 0 .trueLine + first 0 .complementLine =
        world.environment.supply)
    (htime0 : 0 ≤ time)
    (htimeHorizon : time ≤ horizon) :
    first time = second time := by
  have hThreshold :
      world.fabricated.nThreshold =
        world.fabricated.pThreshold := by
    rw [hnThreshold, hpThreshold]
  have hBeta :
      world.fabricated.nBeta = world.fabricated.pBeta := by
    rw [hnBeta, hpBeta]
  have hBetaNonnegative : 0 ≤ world.fabricated.nBeta := by
    rw [hnBeta]
    norm_num
  have hCapacitance :
      world.fabricated.trueCapacitance =
        world.fabricated.complementCapacitance := by
    rw [hTrueCap, hComplementCap]
  have hCapacitancePositive :
      0 < world.fabricated.trueCapacitance := by
    rw [hTrueCap]
    norm_num
  have hsecondInitialBalanced :
      second 0 .trueLine + second 0 .complementLine =
        world.environment.supply := by
    rw [← hinitial]
    exact hinitialBalanced
  have hfirstBalanced :=
    dramDifferentialSense_balanced_invariant_on_domain
      hThreshold hBeta hBetaNonnegative hCapacitance
      hCapacitancePositive hfirst hfirstDomain hinitialBalanced
  have hsecondBalanced :=
    dramDifferentialSense_balanced_invariant_on_domain
      hThreshold hBeta hBetaNonnegative hCapacitance
      hCapacitancePositive hsecond hsecondDomain
      hsecondInitialBalanced
  have hfirstScalar :=
    dramDifferentialSense_balanced_ac_project
      hThreshold hBeta hCapacitance hCapacitancePositive
      hfirst hfirstBalanced
  have hsecondScalar :=
    dramDifferentialSense_balanced_ac_project
      hThreshold hBeta hCapacitance hCapacitancePositive
      hsecond hsecondBalanced
  have hinitialDeviation :
      dramDifferentialSenseTraceDeviation first 0 =
        dramDifferentialSenseTraceDeviation second 0 := by
    unfold dramDifferentialSenseTraceDeviation
      dramDifferentialSenseStateDeviation
    rw [hinitial]
  have hdeviation :=
    dramDifferentialSense_nominal_scalar_determinate
      hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
      hfirstScalar hsecondScalar hinitialDeviation
      htime0 htimeHorizon
  have hfirstSum := hfirstBalanced time htime0 htimeHorizon
  have hsecondSum := hsecondBalanced time htime0 htimeHorizon
  funext index
  cases index <;>
    dsimp [dramDifferentialSenseTraceDeviation,
      dramDifferentialSenseStateDeviation] at hdeviation <;>
    linarith

/-- Primitive two-node DAE realizability across all three nominal MOS
regions. This is the source-level companion to the reduced scalar theorem:
the returned voltage trace satisfies the four MOS and two capacitor equations,
not merely the closed scalar formula. -/
theorem dramDifferentialSense_nominal_vector_realizable
    {world : DramDifferentialSenseWorld}
    {initialDeviation horizon : ℝ}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000)
    (hComplementCap :
      world.fabricated.complementCapacitance =
        3 / 10000000000000)
    (hinitial0 : 0 ≤ initialDeviation)
    (hinitialRail : initialDeviation ≤ 5 / 2)
    (hhorizon : 0 ≤ horizon) :
    ∃ trajectory : DenseTrace ℝ,
      trajectory 0 = initialDeviation ∧
      dramDifferentialSenseDAE.ACBehavesOn world horizon
        (dramDifferentialSenseBalancedTrace world trajectory) ∧
      ∀ time, 0 ≤ time → time ≤ horizon →
        0 ≤ trajectory time ∧ trajectory time ≤ 5 / 2 := by
  obtain ⟨trajectory, hinitial, hscalar, hinvariant⟩ :=
    dramDifferentialSense_nominal_scalar_realizable
      hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
      hinitial0 hinitialRail hhorizon
  have hThreshold :
      world.fabricated.nThreshold =
        world.fabricated.pThreshold := by
    rw [hnThreshold, hpThreshold]
  have hBeta :
      world.fabricated.nBeta = world.fabricated.pBeta := by
    rw [hnBeta, hpBeta]
  have hCapacitance :
      world.fabricated.trueCapacitance =
        world.fabricated.complementCapacitance := by
    rw [hTrueCap, hComplementCap]
  have hCapacitancePositive :
      0 < world.fabricated.trueCapacitance := by
    rw [hTrueCap]
    norm_num
  exact ⟨trajectory, hinitial,
    dramDifferentialSense_balanced_ac_lift
      hThreshold hBeta hCapacitance hCapacitancePositive hscalar,
    hinvariant⟩

noncomputable def dramDifferentialSenseBalancedBoundary
    (world : DramDifferentialSenseWorld)
    (trajectory : DenseTrace ℝ) :
    DramDifferentialSenseBoundary :=
  ⟨dramDifferentialSenseBalancedTrace world trajectory⟩

/-- Full component-level finite-horizon realizability. Initial voltages are
environment constraints; evolution is supplied only by the primitive
source-derived DAE. The rail-domain conclusion is outside the behavior
relation and is proved from the constructed trajectory. -/
theorem dramDifferentialSense_nominal_behavior_realizable
    {world : DramDifferentialSenseWorld}
    {initialDeviation : ℝ}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000)
    (hComplementCap :
      world.fabricated.complementCapacitance =
        3 / 10000000000000)
    (hinitial0 : 0 ≤ initialDeviation)
    (hinitialRail : initialDeviation ≤ 5 / 2)
    (hhorizon : 0 ≤ world.environment.horizon)
    (hTrue :
      world.environment.initialTrue = 5 / 2 + initialDeviation)
    (hComplement :
      world.environment.initialComplement =
        5 / 2 - initialDeviation) :
    ∃ trajectory : DenseTrace ℝ,
      trajectory 0 = initialDeviation ∧
      DramDifferentialSenseBehavior world
        (dramDifferentialSenseBalancedBoundary world trajectory) () ∧
      ∀ time, 0 ≤ time → time ≤ world.environment.horizon →
        0 ≤ trajectory time ∧ trajectory time ≤ 5 / 2 := by
  obtain ⟨trajectory, hinitial, hevolution, hinvariant⟩ :=
    dramDifferentialSense_nominal_vector_realizable
      hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
      hComplementCap hinitial0 hinitialRail hhorizon
  refine ⟨trajectory, hinitial, ?_, hinvariant⟩
  intro clause
  cases clause
  · change
      (dramDifferentialSenseBalancedBoundary
        world trajectory).voltage 0 .trueLine =
      world.environment.initialTrue
    simp [dramDifferentialSenseBalancedBoundary,
      dramDifferentialSenseBalancedTrace,
      dramDifferentialSenseBalancedState,
      hinitial, hsupply, hTrue]
  · change
      (dramDifferentialSenseBalancedBoundary
        world trajectory).voltage 0 .complementLine =
      world.environment.initialComplement
    simp [dramDifferentialSenseBalancedBoundary,
      dramDifferentialSenseBalancedTrace,
      dramDifferentialSenseBalancedState,
      hinitial, hsupply, hComplement]
  · exact hevolution

/-- Exact small-signal trajectory in the first MOS operating region. The
`10^9 s⁻¹` rate is derived above from the source deck's `KP` and load
capacitance; it is not simulator data. -/
noncomputable def dramDifferentialSenseSmallSignalTrace
    (initialDeviation : ℝ) : DenseTrace ℝ :=
  fun time =>
    initialDeviation * Real.exp (1000000000 * time)

theorem dramDifferentialSenseSmallSignalTrace_derivative
    (initialDeviation time : ℝ) :
    HasDerivAt
      (dramDifferentialSenseSmallSignalTrace initialDeviation)
      (1000000000 *
        dramDifferentialSenseSmallSignalTrace initialDeviation time)
      time := by
  change HasDerivAt
    (fun t : ℝ =>
      initialDeviation * Real.exp (1000000000 * t))
    (1000000000 *
      (initialDeviation * Real.exp (1000000000 * time)))
    time
  let inner : ℝ → ℝ := fun t => 1000000000 * t
  have hinner :
      HasDerivAt inner
        1000000000 time := by
    simpa only [inner, id_eq, mul_one] using
      (hasDerivAt_id time).const_mul 1000000000
  have hexponential :
      HasDerivAt (fun t : ℝ => Real.exp (inner t))
        (Real.exp (inner time) * 1000000000) time :=
    (Real.hasDerivAt_exp (inner time)).comp time hinner
  have hscaled := hexponential.const_mul initialDeviation
  simpa only [inner, mul_assoc, mul_comm, mul_left_comm] using hscaled

theorem dramDifferentialSenseSmallSignalTrace_absolutelyContinuous
    (initialDeviation horizon : ℝ) :
    AbsolutelyContinuousOnInterval
      (dramDifferentialSenseSmallSignalTrace initialDeviation)
      0 horizon := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  exact
    (contDiff_const.mul
      (Real.contDiff_exp.comp
        (contDiff_const.mul contDiff_id))).contDiffOn

theorem dramDifferentialSenseSmallSignalTrace_nonnegative
    {initialDeviation time : ℝ}
    (hinitial : 0 ≤ initialDeviation) :
    0 ≤ dramDifferentialSenseSmallSignalTrace initialDeviation time := by
  exact mul_nonneg hinitial (Real.exp_pos _).le

theorem dramDifferentialSenseSmallSignalTrace_le_horizon
    {initialDeviation time horizon : ℝ}
    (hinitial : 0 ≤ initialDeviation)
    (htime : time ≤ horizon) :
    dramDifferentialSenseSmallSignalTrace initialDeviation time ≤
      dramDifferentialSenseSmallSignalTrace
        initialDeviation horizon := by
  unfold dramDifferentialSenseSmallSignalTrace
  apply mul_le_mul_of_nonneg_left _ hinitial
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- The exact small-signal witness is monotone toward the selected rail.
This is a property of the derived exponential trajectory, not an assumption
in the primitive equation program. -/
theorem dramDifferentialSenseSmallSignalTrace_monotone
    {initialDeviation earlier later : ℝ}
    (hinitial : 0 ≤ initialDeviation)
    (htimes : earlier ≤ later) :
    dramDifferentialSenseSmallSignalTrace initialDeviation earlier ≤
      dramDifferentialSenseSmallSignalTrace initialDeviation later :=
  dramDifferentialSenseSmallSignalTrace_le_horizon hinitial htimes

/-- A requested scalar differential is reached by the logarithmic deadline
of the exact first-region trajectory. -/
theorem dramDifferentialSenseSmallSignalTrace_reaches
    {initialDeviation required time : ℝ}
    (hinitial : 0 < initialDeviation)
    (hrequired : 0 < required)
    (htime :
      Real.log (required / initialDeviation) / 1000000000 ≤ time) :
    required ≤
      dramDifferentialSenseSmallSignalTrace initialDeviation time := by
  have hrate : (0 : ℝ) < 1000000000 := by norm_num
  have hratio : 0 < required / initialDeviation :=
    div_pos hrequired hinitial
  have hlog :
      Real.log (required / initialDeviation) ≤
        1000000000 * time :=
    by
      simpa [mul_comm] using (div_le_iff₀ hrate).mp htime
  have hexponential :
      required / initialDeviation ≤
        Real.exp (1000000000 * time) := by
    rw [← Real.exp_log hratio]
    exact Real.exp_le_exp.mpr hlog
  have hscaled :=
    mul_le_mul_of_nonneg_left hexponential hinitial.le
  unfold dramDifferentialSenseSmallSignalTrace
  calc
    required =
        initialDeviation * (required / initialDeviation) := by
          field_simp [hinitial.ne']
    _ ≤ initialDeviation * Real.exp (1000000000 * time) :=
      hscaled

/-- While the exponential witness remains below `1/2 V` differential, its
derivative is exactly the source-derived scalar field. -/
theorem dramDifferentialSense_small_signal_field
    {world : DramDifferentialSenseWorld}
    {initialDeviation time horizon : ℝ}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000)
    (hinitial : 0 ≤ initialDeviation)
    (_htime0 : 0 ≤ time)
    (htimeHorizon : time ≤ horizon)
    (hsmall :
      dramDifferentialSenseSmallSignalTrace
          initialDeviation horizon ≤
        1 / 2) :
    dramDifferentialSenseBalancedRate world
        (dramDifferentialSenseSmallSignalTrace
          initialDeviation time) =
      1000000000 *
        dramDifferentialSenseSmallSignalTrace initialDeviation time := by
  have htrace0 :=
    dramDifferentialSenseSmallSignalTrace_nonnegative
      (time := time) hinitial
  have htraceSmall :
      dramDifferentialSenseSmallSignalTrace initialDeviation time ≤
        1 / 2 :=
    (dramDifferentialSenseSmallSignalTrace_le_horizon
      hinitial htimeHorizon).trans hsmall
  rw [dramDifferentialSense_nominal_balanced_rate_eq
    hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
    htrace0 (by linarith)]
  unfold dramDifferentialSenseNominalBalancedRate
  rw [if_pos htraceSmall]

/-- The exponential witness is a physical scalar DAE trajectory for every
finite horizon that remains in the first MOS region. -/
theorem dramDifferentialSense_small_signal_scalar_behavior
    {world : DramDifferentialSenseWorld}
    {initialDeviation horizon : ℝ}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000)
    (hinitial : 0 ≤ initialDeviation)
    (hhorizon : 0 ≤ horizon)
    (hsmall :
      dramDifferentialSenseSmallSignalTrace
          initialDeviation horizon ≤
        1 / 2) :
    dramDifferentialSenseBalancedDAE.ACBehavesOn world horizon
      (dramDifferentialSenseSmallSignalTrace initialDeviation) := by
  apply ScalarDAE.acBehavesOn_of_smooth
  · exact dramDifferentialSenseSmallSignalTrace_absolutelyContinuous
      initialDeviation horizon
  · refine ⟨hhorizon, ?_⟩
    intro time htime0 htimeHorizon
    refine
      ⟨1000000000 *
          dramDifferentialSenseSmallSignalTrace initialDeviation time,
        dramDifferentialSenseSmallSignalTrace_derivative
          initialDeviation time, ?_⟩
    unfold dramDifferentialSenseBalancedDAE
    exact (dramDifferentialSense_small_signal_field
      hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
      hinitial htime0 htimeHorizon hsmall).symm

/-- Uniqueness of the reduced scalar DAE while it remains in the first MOS
region. Multiplication by `exp (-10^9 t)` turns every such physical
trajectory into an absolutely-continuous function with zero derivative. -/
theorem dramDifferentialSense_small_signal_scalar_eq_trace
    {world : DramDifferentialSenseWorld}
    {deviation : DenseTrace ℝ}
    {initialDeviation horizon time : ℝ}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000)
    (hbehavior :
      dramDifferentialSenseBalancedDAE.ACBehavesOn
        world horizon deviation)
    (hinitial : deviation 0 = initialDeviation)
    (hdomain :
      ∀ point, 0 ≤ point → point ≤ horizon →
        0 ≤ deviation point ∧ deviation point ≤ 1 / 2)
    (htime0 : 0 ≤ time)
    (htimeHorizon : time ≤ horizon) :
    deviation time =
      dramDifferentialSenseSmallSignalTrace initialDeviation time := by
  let integrating : ℝ → ℝ := fun point =>
    Real.exp (-1000000000 * point) * deviation point
  have hexponentialAC :
      AbsolutelyContinuousOnInterval
        (fun point : ℝ => Real.exp (-1000000000 * point))
        0 horizon := by
    apply ContDiffOn.absolutelyContinuousOnInterval
    exact
      (Real.contDiff_exp.comp
        (contDiff_const.mul contDiff_id)).contDiffOn
  have hintegratingAC :
      AbsolutelyContinuousOnInterval integrating 0 horizon :=
    hexponentialAC.mul hbehavior.2.1
  have hintegratingDerivative :
      ∀ᵐ point ∂MeasureTheory.volume.restrict
          (Set.uIcc (0 : ℝ) horizon),
        HasDerivAt integrating 0 point := by
    filter_upwards
      [hbehavior.2.2,
        MeasureTheory.ae_restrict_mem measurableSet_uIcc]
      with point hpoint hpointDomain
    obtain ⟨derivative, hdeviation, hresidual⟩ := hpoint
    rw [Set.uIcc_of_le hbehavior.1] at hpointDomain
    have hvalueDomain :=
      hdomain point hpointDomain.1 hpointDomain.2
    have hfield :
        dramDifferentialSenseBalancedRate world
            (deviation point) =
          1000000000 * deviation point := by
      rw [dramDifferentialSense_nominal_balanced_rate_eq
        hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
        hvalueDomain.1 (by linarith)]
      unfold dramDifferentialSenseNominalBalancedRate
      rw [if_pos hvalueDomain.2]
    change
      derivative =
        dramDifferentialSenseBalancedRate world
          (deviation point) at hresidual
    have hderivative :
        derivative = 1000000000 * deviation point :=
      hresidual.trans hfield
    have hinner :
        HasDerivAt (fun x : ℝ => -1000000000 * x)
          (-1000000000) point := by
      simpa only [id_eq, mul_one] using
        (hasDerivAt_id point).const_mul (-1000000000)
    have hexponential :
        HasDerivAt
          (fun x : ℝ => Real.exp (-1000000000 * x))
          (Real.exp (-1000000000 * point) *
            (-1000000000)) point :=
      (Real.hasDerivAt_exp (-1000000000 * point)).comp
        point hinner
    have hproduct := hexponential.mul hdeviation
    apply hproduct.congr_deriv
    rw [hderivative]
    ring
  have hintegratingDerivative' :
      ∀ᵐ point, point ∈ Set.uIcc (0 : ℝ) horizon →
        HasDerivAt integrating 0 point :=
    MeasureTheory.ae_imp_of_ae_restrict
      hintegratingDerivative
  obtain ⟨constant, hconstantOn⟩ :=
    hintegratingAC.const_of_ae_hasDerivAt_zero
      hintegratingDerivative'
  have hconstant :
      integrating time = integrating 0 :=
    (hconstantOn time
      (by
        rw [Set.uIcc_of_le hbehavior.1]
        exact ⟨htime0, htimeHorizon⟩)).trans
      (hconstantOn 0 (by simp)).symm
  dsimp [integrating] at hconstant
  rw [hinitial] at hconstant
  simp only [mul_zero, Real.exp_zero, one_mul] at hconstant
  have hexponentialProduct :
      Real.exp (-1000000000 * time) *
          Real.exp (1000000000 * time) =
        1 := by
    calc
      Real.exp (-1000000000 * time) *
          Real.exp (1000000000 * time) =
        Real.exp
          (-1000000000 * time + 1000000000 * time) := by
            rw [Real.exp_add]
      _ = Real.exp 0 := by ring_nf
      _ = 1 := Real.exp_zero
  unfold dramDifferentialSenseSmallSignalTrace
  calc
    deviation time =
        (Real.exp (-1000000000 * time) *
            Real.exp (1000000000 * time)) *
          deviation time := by rw [hexponentialProduct, one_mul]
    _ =
        Real.exp (1000000000 * time) *
          (Real.exp (-1000000000 * time) * deviation time) := by
            ring
    _ = Real.exp (1000000000 * time) * initialDeviation := by
      rw [hconstant]
    _ = initialDeviation * Real.exp (1000000000 * time) := by
      ring

/-- A genuine nonconstant transient of the reduced DAE lifts into the
primitive source-backed two-node physical behavior. -/
theorem dramDifferentialSense_small_signal_vector_behavior
    {world : DramDifferentialSenseWorld}
    {initialDeviation horizon : ℝ}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000)
    (hComplementCap :
      world.fabricated.complementCapacitance =
        3 / 10000000000000)
    (hinitial : 0 ≤ initialDeviation)
    (hhorizon : 0 ≤ horizon)
    (hsmall :
      dramDifferentialSenseSmallSignalTrace
          initialDeviation horizon ≤
        1 / 2) :
    dramDifferentialSenseDAE.ACBehavesOn world horizon
      (dramDifferentialSenseBalancedTrace world
        (dramDifferentialSenseSmallSignalTrace initialDeviation)) := by
  have hThreshold :
      world.fabricated.nThreshold =
        world.fabricated.pThreshold := by
    rw [hnThreshold, hpThreshold]
  have hBeta :
      world.fabricated.nBeta = world.fabricated.pBeta := by
    rw [hnBeta, hpBeta]
  have hCapacitance :
      world.fabricated.trueCapacitance =
        world.fabricated.complementCapacitance := by
    rw [hTrueCap, hComplementCap]
  have hCapacitancePositive :
      0 < world.fabricated.trueCapacitance := by
    rw [hTrueCap]
    norm_num
  apply dramDifferentialSense_balanced_ac_lift
    hThreshold hBeta hCapacitance hCapacitancePositive
  exact dramDifferentialSense_small_signal_scalar_behavior
    hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
    hinitial hhorizon hsmall

noncomputable def dramDifferentialSenseSmallSignalBoundary
    (world : DramDifferentialSenseWorld)
    (initialDeviation : ℝ) : DramDifferentialSenseBoundary :=
  ⟨dramDifferentialSenseBalancedTrace world
    (dramDifferentialSenseSmallSignalTrace initialDeviation)⟩

/-- The named exponential witness satisfies the complete equation program.
The initial node voltages are explicit environment equalities, and the only
evolution fact is the source-derived DAE witness above. -/
theorem dramDifferentialSense_small_signal_behavior
    {world : DramDifferentialSenseWorld}
    {initialDeviation : ℝ}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000)
    (hComplementCap :
      world.fabricated.complementCapacitance =
        3 / 10000000000000)
    (hinitial : 0 ≤ initialDeviation)
    (hhorizon : 0 ≤ world.environment.horizon)
    (hsmall :
      dramDifferentialSenseSmallSignalTrace initialDeviation
          world.environment.horizon ≤
        1 / 2)
    (hTrue :
      world.environment.initialTrue = 5 / 2 + initialDeviation)
    (hComplement :
      world.environment.initialComplement =
        5 / 2 - initialDeviation) :
    DramDifferentialSenseBehavior world
      (dramDifferentialSenseSmallSignalBoundary
        world initialDeviation) () := by
  intro clause
  cases clause
  · change
      (dramDifferentialSenseSmallSignalBoundary
        world initialDeviation).voltage 0 .trueLine =
      world.environment.initialTrue
    simp [dramDifferentialSenseSmallSignalBoundary,
      dramDifferentialSenseBalancedTrace,
      dramDifferentialSenseBalancedState,
      dramDifferentialSenseSmallSignalTrace, hsupply, hTrue]
  · change
      (dramDifferentialSenseSmallSignalBoundary
        world initialDeviation).voltage 0 .complementLine =
      world.environment.initialComplement
    simp [dramDifferentialSenseSmallSignalBoundary,
      dramDifferentialSenseBalancedTrace,
      dramDifferentialSenseBalancedState,
      dramDifferentialSenseSmallSignalTrace, hsupply, hComplement]
  · exact dramDifferentialSense_small_signal_vector_behavior
      hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
      hComplementCap hinitial hhorizon hsmall

/-- Packaged transient realizability companion for the universal equation
program. -/
theorem dramDifferentialSense_small_signal_realizable
    {world : DramDifferentialSenseWorld}
    {initialDeviation : ℝ}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000)
    (hComplementCap :
      world.fabricated.complementCapacitance =
        3 / 10000000000000)
    (hinitial : 0 ≤ initialDeviation)
    (hhorizon : 0 ≤ world.environment.horizon)
    (hsmall :
      dramDifferentialSenseSmallSignalTrace initialDeviation
          world.environment.horizon ≤
        1 / 2)
    (hTrue :
      world.environment.initialTrue = 5 / 2 + initialDeviation)
    (hComplement :
      world.environment.initialComplement =
        5 / 2 - initialDeviation) :
    ∃ boundary,
      DramDifferentialSenseBehavior world boundary () :=
  ⟨dramDifferentialSenseSmallSignalBoundary world initialDeviation,
    dramDifferentialSense_small_signal_behavior
      hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
      hComplementCap hinitial hhorizon hsmall hTrue hComplement⟩

/-- Across the whole positive balanced basin, the primitive DAE forces the
selected node upward and its complement downward at equal rates. This is the
pointwise invariant and direction certificate needed by the later global
trajectory proof. -/
theorem dramDifferentialSense_nominal_balanced_regeneration
    {world : DramDifferentialSenseWorld} {time deviation : ℝ}
    {derivative : VectorState DramDifferentialSenseIndex}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000)
    (hComplementCap :
      world.fabricated.complementCapacitance =
        3 / 10000000000000)
    (hdeviation : 0 < deviation)
    (hdeviationRail : deviation < 5 / 2)
    (hresidual :
      dramDifferentialSenseDAE.residual world time
        (dramDifferentialSenseBalancedState 5 deviation)
        derivative) :
    0 < derivative .trueLine ∧
      derivative .complementLine < 0 ∧
      derivative .trueLine + derivative .complementLine = 0 := by
  have hThreshold :
      world.fabricated.nThreshold =
        world.fabricated.pThreshold := by
    rw [hnThreshold, hpThreshold]
  have hBeta :
      world.fabricated.nBeta = world.fabricated.pBeta := by
    rw [hnBeta, hpBeta]
  have hCapacitance :
      world.fabricated.trueCapacitance =
        world.fabricated.complementCapacitance := by
    rw [hTrueCap, hComplementCap]
  have hCapacitancePositive :
      0 < world.fabricated.trueCapacitance := by
    rw [hTrueCap]
    norm_num
  have hrates :=
    (dramDifferentialSense_balanced_residual_iff
      hThreshold hBeta hCapacitance hCapacitancePositive).1
      (by simpa [hsupply] using hresidual)
  have hrate :=
    dramDifferentialSense_nominal_balanced_rate_positive
      hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
      hdeviation hdeviationRail
  rw [hrates.1, hrates.2]
  exact ⟨hrate, neg_lt_zero.mpr hrate, by ring⟩

/-- Both complementary rail assignments are genuine zero-current
equilibria of the primitive DAE. -/
theorem dramDifferentialSense_rail_equilibrium
    (world : DramDifferentialSenseWorld)
    (hnThreshold : 0 ≤ world.fabricated.nThreshold)
    (hpThreshold : 0 ≤ world.fabricated.pThreshold)
    (value : Bool) :
    dramDifferentialSenseDAE.Equilibrium world
      (dramDifferentialSenseRailState world.environment.supply value) := by
  cases value <;>
    simp [VectorDAE.Equilibrium, dramDifferentialSenseDAE,
      dramDifferentialSenseRailState,
      dramDifferentialSenseNCurrent, dramDifferentialSensePCurrent,
      mos1ForwardCurrent, hnThreshold, hpThreshold] <;>
    constructor <;> intro hlt hgt <;> linarith

/-- With matched N/P thresholds and strengths, the common-mode midpoint is
also an equilibrium. This is the metastable state that a valid margin theorem
must exclude rather than assume away. -/
theorem dramDifferentialSense_metastable_equilibrium
    (world : DramDifferentialSenseWorld)
    (hThreshold :
      world.fabricated.nThreshold = world.fabricated.pThreshold)
    (hBeta : world.fabricated.nBeta = world.fabricated.pBeta) :
    dramDifferentialSenseDAE.Equilibrium world
      (dramDifferentialSenseMetastableState
        world.environment.supply) := by
  have hhalf :
      world.environment.supply - world.environment.supply / 2 =
        world.environment.supply / 2 := by
    ring
  have hcurrent :
      dramDifferentialSenseNCurrent world.fabricated
          (world.environment.supply / 2)
          (world.environment.supply / 2) =
        dramDifferentialSensePCurrent world.fabricated
          world.environment.supply
          (world.environment.supply / 2)
          (world.environment.supply / 2) := by
    unfold dramDifferentialSenseNCurrent
      dramDifferentialSensePCurrent
    rw [hhalf]
    simp [mos1ForwardCurrent, hThreshold, hBeta]
  simp only [VectorDAE.Equilibrium, dramDifferentialSenseDAE,
    dramDifferentialSenseMetastableState]
  exact ⟨by linarith, by linarith⟩

/-- In the nominal matched deck, a small positive differential around the
metastable common mode is locally regenerative: the DAE forces the
true-minus-complement derivative to be positive. The `deviation < 1/2`
restriction is the MOS1 region in which all four devices remain in the
matched saturation branches. -/
theorem dramDifferentialSense_nominal_local_regeneration
    {world : DramDifferentialSenseWorld} {time deviation : ℝ}
    {derivative : VectorState DramDifferentialSenseIndex}
    (hsupply : world.environment.supply = 5)
    (hnThreshold : world.fabricated.nThreshold = 1)
    (hpThreshold : world.fabricated.pThreshold = 1)
    (hnBeta : world.fabricated.nBeta = 1 / 10000)
    (hpBeta : world.fabricated.pBeta = 1 / 10000)
    (hTrueCap :
      world.fabricated.trueCapacitance = 3 / 10000000000000)
    (hComplementCap :
      world.fabricated.complementCapacitance =
        3 / 10000000000000)
    (hdeviation : 0 < deviation)
    (hregion : deviation < 1 / 2)
    (hresidual :
      dramDifferentialSenseDAE.residual world time
        (dramDifferentialSenseBalancedState 5 deviation)
        derivative) :
    0 < derivative .trueLine - derivative .complementLine := by
  have hdirection :=
    dramDifferentialSense_nominal_balanced_regeneration
      hsupply hnThreshold hpThreshold hnBeta hpBeta hTrueCap
      hComplementCap hdeviation (by linarith) hresidual
  linarith

/-- The nominal source-deck latch amplifies every positive differential in
the rail rectangle, not only states whose common mode is exactly balanced.
The only zero-rate endpoint in this ordered half of the rectangle is the
already-resolved `(VDD, 0)` rail state. -/
theorem dramDifferentialSense_nominal_force_order
    {trueVoltage complementVoltage : ℝ}
    (_htrue0 : 0 ≤ trueVoltage)
    (htrue5 : trueVoltage ≤ 5)
    (hcomplement0 : 0 ≤ complementVoltage)
    (hcomplement5 : complementVoltage ≤ 5)
    (horder : complementVoltage < trueVoltage)
    (hnotRail : trueVoltage < 5 ∨ 0 < complementVoltage) :
    dramDifferentialSensePCurrent
          nominalDramDifferentialSenseInstance 5
          complementVoltage trueVoltage -
        dramDifferentialSenseNCurrent
          nominalDramDifferentialSenseInstance
          complementVoltage trueVoltage >
      dramDifferentialSensePCurrent
          nominalDramDifferentialSenseInstance 5
          trueVoltage complementVoltage -
        dramDifferentialSenseNCurrent
          nominalDramDifferentialSenseInstance
          trueVoltage complementVoltage := by
  have hnOrder :
      dramDifferentialSenseNCurrent
          nominalDramDifferentialSenseInstance
          complementVoltage trueVoltage ≤
        dramDifferentialSenseNCurrent
          nominalDramDifferentialSenseInstance
          trueVoltage complementVoltage := by
    exact mos1ForwardCurrent_cross_mono_zero_lambda
      .nmos 1 (1 / 10000) complementVoltage trueVoltage
      (by norm_num) (by norm_num) hcomplement0 horder.le
  have hpOrder :
      dramDifferentialSensePCurrent
          nominalDramDifferentialSenseInstance 5
          trueVoltage complementVoltage ≤
        dramDifferentialSensePCurrent
          nominalDramDifferentialSenseInstance 5
          complementVoltage trueVoltage := by
    exact mos1ForwardCurrent_cross_mono_zero_lambda
      .pmos 1 (1 / 10000)
      (5 - trueVoltage) (5 - complementVoltage)
      (by norm_num) (by norm_num) (by linarith) (by linarith)
  rcases le_or_gt trueVoltage 1 with htrueBelow | htrueAbove
  · have hpStrict :
        dramDifferentialSensePCurrent
            nominalDramDifferentialSenseInstance 5
            trueVoltage complementVoltage <
          dramDifferentialSensePCurrent
            nominalDramDifferentialSenseInstance 5
            complementVoltage trueVoltage := by
      exact mos1ForwardCurrent_cross_strict_zero_lambda
        .pmos 1 (1 / 10000)
        (5 - trueVoltage) (5 - complementVoltage)
        (by norm_num) (by norm_num) (by linarith) (by linarith)
        (by linarith)
    linarith
  · rcases eq_or_lt_of_le hcomplement0 with hcomplementZero
      | hcomplementPositive
    · subst complementVoltage
      have htrueBelowRail : trueVoltage < 5 := by
        rcases hnotRail with h | h
        · exact h
        · linarith
      have hpStrict :
          dramDifferentialSensePCurrent
              nominalDramDifferentialSenseInstance 5
              trueVoltage 0 <
          dramDifferentialSensePCurrent
              nominalDramDifferentialSenseInstance 5
              0 trueVoltage := by
        simpa [dramDifferentialSensePCurrent,
          nominalDramDifferentialSenseInstance] using
          (mos1ForwardCurrent_cross_strict_zero_lambda
            .pmos 1 (1 / 10000) (5 - trueVoltage) 5
            (by norm_num) (by norm_num) (by linarith) (by norm_num)
            (by linarith))
      linarith
    · have hnStrict :
          dramDifferentialSenseNCurrent
              nominalDramDifferentialSenseInstance
              complementVoltage trueVoltage <
            dramDifferentialSenseNCurrent
              nominalDramDifferentialSenseInstance
              trueVoltage complementVoltage := by
        exact mos1ForwardCurrent_cross_strict_zero_lambda
          .nmos 1 (1 / 10000) complementVoltage trueVoltage
          (by norm_num) (by norm_num) hcomplementPositive
          (by linarith) horder
      linarith

/-- At every ordered, nonterminal state in the nominal source-deck rail
rectangle, the primitive capacitor KCL equations force the two node voltages
farther apart. Unlike the balanced-manifold theorem, this allows arbitrary
common-mode error. -/
theorem dramDifferentialSense_nominal_unbalanced_regeneration
    {world : DramDifferentialSenseWorld} {time : ℝ}
    {state derivative : VectorState DramDifferentialSenseIndex}
    (hsupply : world.environment.supply = 5)
    (hinstance :
      world.fabricated = nominalDramDifferentialSenseInstance)
    (hstate :
      DramDifferentialSenseStateInRailDomain world state)
    (horder : state .complementLine < state .trueLine)
    (hnotRail :
      state .trueLine < 5 ∨ 0 < state .complementLine)
    (hresidual :
      dramDifferentialSenseDAE.residual world time state derivative) :
    0 < derivative .trueLine - derivative .complementLine := by
  change
    0 ≤ state .trueLine ∧
      state .trueLine ≤ world.environment.supply ∧
      0 ≤ state .complementLine ∧
      state .complementLine ≤ world.environment.supply at hstate
  rw [hsupply] at hstate
  rcases hstate with
    ⟨htrue0, htrue5, hcomplement0, hcomplement5⟩
  have hforce :=
    dramDifferentialSense_nominal_force_order
      htrue0 htrue5 hcomplement0 hcomplement5 horder hnotRail
  change
    world.fabricated.trueCapacitance * derivative .trueLine +
          dramDifferentialSenseNCurrent world.fabricated
            (state .complementLine) (state .trueLine) -
          dramDifferentialSensePCurrent world.fabricated
            world.environment.supply
            (state .complementLine) (state .trueLine) = 0 ∧
      world.fabricated.complementCapacitance *
            derivative .complementLine +
          dramDifferentialSenseNCurrent world.fabricated
            (state .trueLine) (state .complementLine) -
          dramDifferentialSensePCurrent world.fabricated
            world.environment.supply
            (state .trueLine) (state .complementLine) = 0 at hresidual
  rw [hinstance, hsupply] at hresidual
  change
    (3 / 10000000000000 : ℝ) * derivative .trueLine +
          dramDifferentialSenseNCurrent
            nominalDramDifferentialSenseInstance
            (state .complementLine) (state .trueLine) -
          dramDifferentialSensePCurrent
            nominalDramDifferentialSenseInstance 5
            (state .complementLine) (state .trueLine) = 0 ∧
      (3 / 10000000000000 : ℝ) * derivative .complementLine +
          dramDifferentialSenseNCurrent
            nominalDramDifferentialSenseInstance
            (state .trueLine) (state .complementLine) -
          dramDifferentialSensePCurrent
            nominalDramDifferentialSenseInstance 5
            (state .trueLine) (state .complementLine) = 0 at hresidual
  norm_num at hresidual
  nlinarith

/-- Symmetric negative-polarity form: when the complement line is higher,
the primitive nominal DAE makes the signed true-minus-complement
differential strictly more negative. -/
theorem dramDifferentialSense_nominal_unbalanced_regeneration_reverse
    {world : DramDifferentialSenseWorld} {time : ℝ}
    {state derivative : VectorState DramDifferentialSenseIndex}
    (hsupply : world.environment.supply = 5)
    (hinstance :
      world.fabricated = nominalDramDifferentialSenseInstance)
    (hstate :
      DramDifferentialSenseStateInRailDomain world state)
    (horder : state .trueLine < state .complementLine)
    (hnotRail :
      state .complementLine < 5 ∨ 0 < state .trueLine)
    (hresidual :
      dramDifferentialSenseDAE.residual world time state derivative) :
    derivative .trueLine - derivative .complementLine < 0 := by
  change
    0 ≤ state .trueLine ∧
      state .trueLine ≤ world.environment.supply ∧
      0 ≤ state .complementLine ∧
      state .complementLine ≤ world.environment.supply at hstate
  rw [hsupply] at hstate
  rcases hstate with
    ⟨htrue0, htrue5, hcomplement0, hcomplement5⟩
  have hforce :=
    dramDifferentialSense_nominal_force_order
      hcomplement0 hcomplement5 htrue0 htrue5 horder hnotRail
  change
    world.fabricated.trueCapacitance * derivative .trueLine +
          dramDifferentialSenseNCurrent world.fabricated
            (state .complementLine) (state .trueLine) -
          dramDifferentialSensePCurrent world.fabricated
            world.environment.supply
            (state .complementLine) (state .trueLine) = 0 ∧
      world.fabricated.complementCapacitance *
            derivative .complementLine +
          dramDifferentialSenseNCurrent world.fabricated
            (state .trueLine) (state .complementLine) -
          dramDifferentialSensePCurrent world.fabricated
            world.environment.supply
            (state .trueLine) (state .complementLine) = 0 at hresidual
  rw [hinstance, hsupply] at hresidual
  change
    (3 / 10000000000000 : ℝ) * derivative .trueLine +
          dramDifferentialSenseNCurrent
            nominalDramDifferentialSenseInstance
            (state .complementLine) (state .trueLine) -
          dramDifferentialSensePCurrent
            nominalDramDifferentialSenseInstance 5
            (state .complementLine) (state .trueLine) = 0 ∧
      (3 / 10000000000000 : ℝ) * derivative .complementLine +
          dramDifferentialSenseNCurrent
            nominalDramDifferentialSenseInstance
            (state .trueLine) (state .complementLine) -
          dramDifferentialSensePCurrent
            nominalDramDifferentialSenseInstance 5
            (state .trueLine) (state .complementLine) = 0 at hresidual
  norm_num at hresidual
  nlinarith

private theorem dramDifferentialSense_constant_physical
    {world : DramDifferentialSenseWorld}
    {state : VectorState DramDifferentialSenseIndex}
    (hhorizon : 0 ≤ world.environment.horizon)
    (hequilibrium :
      dramDifferentialSenseDAE.Equilibrium world state) :
    dramDifferentialSenseDAE.ACBehavesOn world
      world.environment.horizon (fun _time => state) := by
  refine ⟨hhorizon, ?_, ?_⟩
  · intro index
    exact (LipschitzWith.const (state index)).lipschitzOnWith
      |>.absolutelyContinuousOnInterval
  · exact MeasureTheory.ae_restrict_of_forall_mem
      measurableSet_uIcc fun time _htime => by
        refine ⟨fun _index => 0, ?_, ?_⟩
        · intro index
          exact hasDerivAt_const time (state index)
        · simpa [VectorDAE.Equilibrium,
            dramDifferentialSenseDAE] using hequilibrium

theorem dramDifferentialSense_constant_realizable
    {world : DramDifferentialSenseWorld}
    {state : VectorState DramDifferentialSenseIndex}
    (hhorizon : 0 ≤ world.environment.horizon)
    (hTrue : state .trueLine = world.environment.initialTrue)
    (hComplement :
      state .complementLine = world.environment.initialComplement)
    (hequilibrium :
      dramDifferentialSenseDAE.Equilibrium world state) :
    ∃ boundary,
      DramDifferentialSenseBehavior world boundary () := by
  refine ⟨⟨fun _time => state⟩, ?_⟩
  intro clause
  cases clause
  · exact hTrue
  · exact hComplement
  · exact dramDifferentialSense_constant_physical hhorizon hequilibrium

theorem dramDifferentialSense_rail_realizable
    {world : DramDifferentialSenseWorld}
    (hadmissible : DramDifferentialSenseAdmissible world)
    (value : Bool)
    (hTrue :
      (dramDifferentialSenseRailState world.environment.supply value)
          .trueLine =
        world.environment.initialTrue)
    (hComplement :
      (dramDifferentialSenseRailState world.environment.supply value)
          .complementLine =
        world.environment.initialComplement) :
    ∃ boundary,
      DramDifferentialSenseBehavior world boundary () :=
  dramDifferentialSense_constant_realizable hadmissible.2.2.2.2.2.2.2.2.2.2.2
    hTrue hComplement
    (dramDifferentialSense_rail_equilibrium world
      hadmissible.2.1 hadmissible.2.2.1 value)

theorem dramDifferentialSense_metastable_realizable
    {world : DramDifferentialSenseWorld}
    (hadmissible : DramDifferentialSenseAdmissible world)
    (hThreshold :
      world.fabricated.nThreshold = world.fabricated.pThreshold)
    (hBeta : world.fabricated.nBeta = world.fabricated.pBeta)
    (hTrue :
      world.environment.initialTrue = world.environment.supply / 2)
    (hComplement :
      world.environment.initialComplement =
        world.environment.supply / 2) :
    ∃ boundary,
      DramDifferentialSenseBehavior world boundary () := by
  apply dramDifferentialSense_constant_realizable
    (state := dramDifferentialSenseMetastableState
      world.environment.supply)
    hadmissible.2.2.2.2.2.2.2.2.2.2.2
  · simpa [dramDifferentialSenseMetastableState] using hTrue.symm
  · simpa [dramDifferentialSenseMetastableState] using hComplement.symm
  · exact dramDifferentialSense_metastable_equilibrium world
      hThreshold hBeta

end LeanModels.Spice

namespace LeanModels.Circuit

def ElaboratedCircuit.toDramDifferentialSense
    (circuit : ElaboratedCircuit) :
    Except String LeanModels.Spice.DramDifferentialSenseLayout :=
  LeanModels.Spice.ElaboratedCircuit.toDramDifferentialSense circuit

end LeanModels.Circuit
