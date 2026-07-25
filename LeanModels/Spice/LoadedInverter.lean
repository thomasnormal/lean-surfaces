import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic
import LeanModels.Circuit
import LeanModels.Spice.Mos1

/-!
# Charge-consistent loaded MOS1 inverter

This slice treats the transistor pair as an open component. Supply and input
drivers are selected by the run world, not embedded as fixed voltage sources.
The supported MOS1 profile has no intrinsic terminal-charge model, so its
intrinsic charge is explicitly zero. Dynamic storage comes from the extracted
load capacitor, whose equal-and-opposite terminal charge is conserved.

The nonlinear current relation is the same long-channel square law used by
`mos1ForwardCurrent`. A globally Lipschitz extension clamps the drain-source
drop to the physical interval. It agrees with MOS1 inside the proved supply
domain and is used only to obtain finite-horizon ODE existence and uniqueness.
-/

namespace LeanModels.Spice

open LeanModels.Circuit
open Set

/-- Charge on the four typed MOS terminals. -/
structure MosTerminalCharge where
  drain : ℝ
  gate : ℝ
  source : ℝ
  bulk : ℝ

/-- Terminal charge is conservative when the device stores no hidden net
charge outside its declared terminals. -/
def MosTerminalCharge.Conservative (charge : MosTerminalCharge) : Prop :=
  charge.drain + charge.gate + charge.source + charge.bulk = 0

/-- The named MOS1 profile is a DC channel model and contributes no intrinsic
terminal charge. Parasitic charge must therefore be an explicit component. -/
def mos1IntrinsicCharge : MosTerminalCharge :=
  { drain := 0, gate := 0, source := 0, bulk := 0 }

theorem mos1IntrinsicCharge_conservative :
    mos1IntrinsicCharge.Conservative := by
  norm_num [MosTerminalCharge.Conservative, mos1IntrinsicCharge]

/-- Equal-and-opposite charge of a two-terminal capacitor. -/
structure CapacitorTerminalCharge where
  positive : ℝ
  negative : ℝ

def loadCapacitorCharge (capacitance voltage : ℝ) :
    CapacitorTerminalCharge :=
  { positive := capacitance * voltage
    negative := -(capacitance * voltage) }

theorem loadCapacitorCharge_conservative (capacitance voltage : ℝ) :
    (loadCapacitorCharge capacitance voltage).positive +
      (loadCapacitorCharge capacitance voltage).negative = 0 := by
  simp [loadCapacitorCharge]

/-- Typed parameters fixed once for a fabricated inverter instance. -/
structure LoadedInverterInstance where
  nThreshold : ℝ
  pThreshold : ℝ
  nBeta : ℝ
  pBeta : ℝ
  loadCapacitance : ℝ

/-- One run of one fabricated inverter. The Boolean input is held at the
selected rail during the finite proof horizon. -/
structure LoadedInverterEnvironment where
  supply : ℝ
  input : Bool
  initialVoltage : ℝ
  horizon : ℝ

abbrev LoadedInverterWorld :=
  RunWorld LoadedInverterInstance LoadedInverterEnvironment Unit Unit

/-- General, correlation-preserving set of fabricated instances. -/
abbrev LoadedInverterInstanceSet := Set LoadedInverterInstance

/-- Exact data recovered from a typed three-device inverter deck. -/
structure LoadedInverterNominal where
  inputNode : LeanModels.Circuit.NodeId
  outputNode : LeanModels.Circuit.NodeId
  supplyNode : LeanModels.Circuit.NodeId
  nThreshold : Rat
  pThreshold : Rat
  nBeta : Rat
  pBeta : Rat
  loadCapacitance : Rat
deriving Repr, BEq, Inhabited

/-- Validate the complete PMOS/NMOS/load-capacitor topology before exposing
parameters to the transient semantics. -/
def ElaboratedCircuit.toLoadedInverterNominal
    (circuit : ElaboratedCircuit) :
    Except String LoadedInverterNominal := do
  if circuit.devices.size != 3 then
    throw s!"loaded inverter requires exactly three devices, found {circuit.devices.size}"
  let mosfets := circuit.devices.toList.filterMap fun
    | .mosfet _ drain gate source bulk model =>
        some (drain, gate, source, bulk, model)
    | _ => none
  let capacitors := circuit.devices.toList.filterMap fun
    | .capacitor _ positive negative value =>
        some (positive, negative, value)
    | _ => none
  let (firstMos, secondMos) ← match mosfets with
    | [first, second] => pure (first, second)
    | _ => throw "loaded inverter requires exactly two MOSFETs"
  let (cPositive, cNegative, capacitance) ← match capacitors with
    | [capacitor] => pure capacitor
    | _ => throw "loaded inverter requires exactly one load capacitor"
  let firstModelId := firstMos.2.2.2.2
  let secondModelId := secondMos.2.2.2.2
  let firstModel ← match circuit.models[firstModelId.index]? with
    | some (.mos1 model) => pure model
    | _ => throw "first MOSFET model is missing or unsupported"
  let secondModel ← match circuit.models[secondModelId.index]? with
    | some (.mos1 model) => pure model
    | _ => throw "second MOSFET model is missing or unsupported"
  let (pMos, pModel, nMos, nModel) ←
    match firstModel.polarity, secondModel.polarity with
    | .pmos, .nmos => pure (firstMos, firstModel, secondMos, secondModel)
    | .nmos, .pmos => pure (secondMos, secondModel, firstMos, firstModel)
    | _, _ => throw "loaded inverter requires one PMOS and one NMOS"
  let output := pMos.1
  let input := pMos.2.1
  let supply := pMos.2.2.1
  let pBulk := pMos.2.2.2.1
  let nOutput := nMos.1
  let nInput := nMos.2.1
  let groundSource := nMos.2.2.1
  let groundBulk := nMos.2.2.2.1
  unless output == nOutput && input == nInput &&
      groundSource == circuit.ground && groundBulk == circuit.ground &&
      pBulk == supply && cPositive == output &&
      cNegative == circuit.ground do
    throw "loaded inverter connectivity does not match the proved topology"
  unless pModel.channelLengthModulation == 0 &&
      nModel.channelLengthModulation == 0 &&
      pModel.junctionSaturation == 0 &&
      nModel.junctionSaturation == 0 do
    throw "loaded inverter requires the named LAMBDA=0, IS=0 MOS1 profile"
  pure
    { inputNode := input
      outputNode := output
      supplyNode := supply
      nThreshold := nModel.threshold
      pThreshold := pModel.threshold
      nBeta := nModel.transconductance
      pBeta := pModel.transconductance
      loadCapacitance := capacitance }

noncomputable def LoadedInverterNominal.instance
    (nominal : LoadedInverterNominal) : LoadedInverterInstance :=
  { nThreshold := nominal.nThreshold
    pThreshold := nominal.pThreshold
    nBeta := nominal.nBeta
    pBeta := nominal.pBeta
    loadCapacitance := nominal.loadCapacitance }

noncomputable def LoadedInverterNominal.world
    (nominal : LoadedInverterNominal) (supply : ℝ) (input : Bool)
    (initialVoltage horizon : ℝ) : LoadedInverterWorld :=
  deterministicWorld nominal.instance
    { supply, input, initialVoltage, horizon }

/-- The nominal model and explicit 1 pF load in the example deck. -/
noncomputable def nominalLoadedInverterInstance : LoadedInverterInstance :=
  { nThreshold := 1
    pThreshold := 1
    nBeta := 1 / 10000
    pBeta := 1 / 20000
    loadCapacitance := 1 / 1000000000000 }

/-- A correlated process/load envelope. The beta ratio is selected once per
fabricated instance; it cannot change adversarially during a run. -/
def LoadedInverterCorners : LoadedInverterInstanceSet :=
  { fabricated |
    9 / 10 ≤ fabricated.nThreshold ∧ fabricated.nThreshold ≤ 11 / 10 ∧
    9 / 10 ≤ fabricated.pThreshold ∧ fabricated.pThreshold ≤ 11 / 10 ∧
    2 / 25000 ≤ fabricated.nBeta ∧ fabricated.nBeta ≤ 3 / 25000 ∧
    fabricated.nBeta = 2 * fabricated.pBeta ∧
    4 / 5000000000000 ≤ fabricated.loadCapacitance ∧
    fabricated.loadCapacitance ≤ 3 / 2500000000000 }

/-- Physical and proof-domain conditions for a finite loaded-inverter run. -/
def LoadedInverterAdmissible (world : LoadedInverterWorld) : Prop :=
  0 < world.fabricated.nBeta ∧
  0 < world.fabricated.pBeta ∧
  0 < world.fabricated.loadCapacitance ∧
  0 < world.fabricated.nThreshold ∧
  world.fabricated.nThreshold < world.environment.supply ∧
  0 < world.fabricated.pThreshold ∧
  world.fabricated.pThreshold < world.environment.supply ∧
  0 ≤ world.environment.initialVoltage ∧
  world.environment.initialVoltage ≤ world.environment.supply ∧
  0 ≤ world.environment.horizon

/-- PVT-robust admissibility: one instance from the correlated set and one
supply from the allowed run environment. -/
def LoadedInverterCornerRun (world : LoadedInverterWorld) : Prop :=
  world.fabricated ∈ LoadedInverterCorners ∧
  9 / 2 ≤ world.environment.supply ∧
  world.environment.supply ≤ 11 / 2 ∧
  0 ≤ world.environment.initialVoltage ∧
  world.environment.initialVoltage ≤ world.environment.supply ∧
  0 ≤ world.environment.horizon

theorem loadedInverterCornerRun_admissible {world : LoadedInverterWorld}
    (hcorner : LoadedInverterCornerRun world) :
    LoadedInverterAdmissible world := by
  rcases hcorner with
    ⟨⟨hnt0, hnt1, hpt0, hpt1, hnb0, hnb1, hratio, hc0, hc1⟩,
      hvdd0, hvdd1, hinitial0, hinitial1, hhorizon⟩
  refine ⟨by linarith, ?_, by linarith, by linarith, by linarith,
    by linarith, by linarith, hinitial0, hinitial1, hhorizon⟩
  nlinarith

/-- Clamp a physical drain-source drop to `[0, overdrive]`. -/
noncomputable def clampedDrop (overdrive drop : ℝ) : ℝ :=
  max 0 (min overdrive drop)

/-- Square-law current as a continuous global extension of the rail-driven
cutoff/triode/saturation relation. -/
noncomputable def railCurrent (beta overdrive drop : ℝ) : ℝ :=
  let effective := clampedDrop overdrive drop
  beta * (overdrive * effective - effective ^ 2 / 2)

theorem clampedDrop_bounds {overdrive drop : ℝ} (hoverdrive : 0 ≤ overdrive) :
    0 ≤ clampedDrop overdrive drop ∧
      clampedDrop overdrive drop ≤ overdrive := by
  unfold clampedDrop
  constructor
  · exact le_max_left _ _
  · exact max_le hoverdrive (min_le_left _ _)

theorem clampedDrop_eq_self {overdrive drop : ℝ}
    (hdrop0 : 0 ≤ drop) (hdrop1 : drop ≤ overdrive) :
    clampedDrop overdrive drop = drop := by
  simp [clampedDrop, hdrop0, hdrop1]

theorem clampedDrop_eq_zero {overdrive drop : ℝ} (hdrop : drop ≤ 0) :
    clampedDrop overdrive drop = 0 := by
  simp [clampedDrop, min_le_of_right_le hdrop]

theorem clampedDrop_eq_overdrive {overdrive drop : ℝ}
    (hoverdrive : 0 ≤ overdrive) (hdrop : overdrive ≤ drop) :
    clampedDrop overdrive drop = overdrive := by
  simp [clampedDrop, hoverdrive, hdrop]

theorem railCurrent_nonneg {beta overdrive drop : ℝ}
    (hbeta : 0 ≤ beta) (hoverdrive : 0 ≤ overdrive) :
    0 ≤ railCurrent beta overdrive drop := by
  obtain ⟨heffective0, heffective1⟩ :=
    clampedDrop_bounds (drop := drop) hoverdrive
  unfold railCurrent
  dsimp
  have hshape :
      0 ≤ overdrive * clampedDrop overdrive drop -
        clampedDrop overdrive drop ^ 2 / 2 := by
    nlinarith [mul_nonneg heffective0
      (show 0 ≤ overdrive - clampedDrop overdrive drop / 2 by linarith)]
  positivity

theorem railCurrent_eq_mos1 {polarity : LeanModels.Circuit.MosPolarity}
    {threshold beta vgs drop : ℝ}
    (_hbeta : 0 ≤ beta) (hon : threshold ≤ vgs) (hdrop : 0 ≤ drop) :
    railCurrent beta (vgs - threshold) drop =
      mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 } vgs drop := by
  unfold mos1ForwardCurrent
  by_cases hcutoff : vgs ≤ threshold
  · have heq : vgs = threshold := le_antisymm hcutoff hon
    subst vgs
    simp [railCurrent, clampedDrop, hdrop]
  · simp only [hcutoff, if_false]
    by_cases htriode : drop ≤ vgs - threshold
    · rw [if_pos htriode]
      unfold railCurrent
      rw [clampedDrop_eq_self hdrop htriode]
      simp
    · rw [if_neg htriode]
      unfold railCurrent
      rw [clampedDrop_eq_overdrive
        (sub_nonneg.mpr hon) (le_of_not_ge htriode)]
      ring

/-- Cutoff is represented by clamping the overdrive to zero. -/
noncomputable def mos1EnvelopeCurrent
    (beta threshold vgs drop : ℝ) : ℝ :=
  railCurrent beta (max 0 (vgs - threshold)) drop

theorem mos1EnvelopeCurrent_eq_mos1 {polarity : LeanModels.Circuit.MosPolarity}
    {threshold beta vgs drop : ℝ}
    (hbeta : 0 ≤ beta) (hdrop : 0 ≤ drop) :
    mos1EnvelopeCurrent beta threshold vgs drop =
      mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 } vgs drop := by
  by_cases hon : threshold ≤ vgs
  · rw [mos1EnvelopeCurrent, max_eq_right (sub_nonneg.mpr hon)]
    exact railCurrent_eq_mos1 hbeta hon hdrop
  · have hcutoff : vgs ≤ threshold := le_of_not_ge hon
    simp [mos1EnvelopeCurrent, mos1ForwardCurrent, hcutoff,
      max_eq_left (sub_nonpos.mpr hcutoff), railCurrent, clampedDrop]

theorem clampedDrop_continuous (overdrive : ℝ) :
    Continuous (clampedDrop overdrive) := by
  exact continuous_const.max (continuous_const.min continuous_id)

theorem railCurrent_continuous (beta overdrive : ℝ) :
    Continuous (railCurrent beta overdrive) := by
  unfold railCurrent
  dsimp
  have heffective := clampedDrop_continuous overdrive
  exact continuous_const.mul
    ((continuous_const.mul heffective).sub
      ((heffective.pow 2).div_const 2))

theorem clampedDrop_lipschitz (overdrive : ℝ) :
    LipschitzWith 1 (clampedDrop overdrive) := by
  change LipschitzWith 1 (fun drop => max 0 (min overdrive drop))
  exact (LipschitzWith.id.const_min overdrive).const_max 0

theorem railCurrent_lipschitz {beta overdrive : ℝ}
    (hbeta : 0 ≤ beta) (hoverdrive : 0 ≤ overdrive) :
    LipschitzWith
      ⟨beta * overdrive, mul_nonneg hbeta hoverdrive⟩
      (railCurrent beta overdrive) := by
  apply LipschitzWith.of_dist_le_mul
  intro left right
  let u := clampedDrop overdrive left
  let v := clampedDrop overdrive right
  obtain ⟨hu0, hu1⟩ :=
    clampedDrop_bounds (drop := left) hoverdrive
  obtain ⟨hv0, hv1⟩ :=
    clampedDrop_bounds (drop := right) hoverdrive
  have hfactor0 : 0 ≤ overdrive - (u + v) / 2 := by
    dsimp [u, v]
    linarith
  have hfactor1 : overdrive - (u + v) / 2 ≤ overdrive := by
    dsimp [u, v]
    linarith
  have hclamp :
      |u - v| ≤ |left - right| := by
    simpa [u, v, Real.dist_eq] using
      (clampedDrop_lipschitz overdrive).dist_le_mul left right
  simp only [Real.dist_eq, NNReal.coe_mk]
  unfold railCurrent
  dsimp only
  change
    |beta * (overdrive * u - u ^ 2 / 2) -
        beta * (overdrive * v - v ^ 2 / 2)| ≤
      beta * overdrive * |left - right|
  calc
    _ = |beta| * |(u - v) * (overdrive - (u + v) / 2)| := by
      rw [← abs_mul]
      congr 1
      ring
    _ = beta * (|u - v| * |overdrive - (u + v) / 2|) := by
      rw [abs_mul, abs_of_nonneg hbeta]
    _ ≤ beta * (|u - v| * overdrive) := by
      gcongr
      rw [abs_of_nonneg hfactor0]
      exact hfactor1
    _ ≤ beta * (|left - right| * overdrive) := by
      gcongr
    _ = beta * overdrive * |left - right| := by ring

theorem railCurrent_le {beta overdrive drop : ℝ}
    (hbeta : 0 ≤ beta) (hoverdrive : 0 ≤ overdrive) :
    railCurrent beta overdrive drop ≤ beta * overdrive ^ 2 / 2 := by
  obtain ⟨heffective0, heffective1⟩ :=
    clampedDrop_bounds (drop := drop) hoverdrive
  unfold railCurrent
  dsimp
  have hshape :
      overdrive * clampedDrop overdrive drop -
          clampedDrop overdrive drop ^ 2 / 2 ≤
        overdrive ^ 2 / 2 := by
    nlinarith [sq_nonneg (overdrive - clampedDrop overdrive drop)]
  nlinarith [mul_le_mul_of_nonneg_left hshape hbeta]

theorem mos1EnvelopeCurrent_continuous
    (beta threshold vgs : ℝ) :
    Continuous (mos1EnvelopeCurrent beta threshold vgs) :=
  railCurrent_continuous _ _

/-- Static KCL relation of the loaded inverter. The capacitor is open at DC. -/
def LoadedInverterDC
    (fabricated : LoadedInverterInstance)
    (supply input output : ℝ) : Prop :=
  0 ≤ output ∧ output ≤ supply ∧
  mos1ForwardCurrent
      { polarity := .nmos, threshold := fabricated.nThreshold,
        beta := fabricated.nBeta, lambda := 0 }
      input output =
  mos1ForwardCurrent
      { polarity := .pmos, threshold := fabricated.pThreshold,
        beta := fabricated.pBeta, lambda := 0 }
      (supply - input) (supply - output)

/-- A low-band input forces the unique DC output to the positive rail. -/
theorem loadedInverter_dc_low
    {fabricated : LoadedInverterInstance} {supply input output : ℝ}
    (hbeta : 0 < fabricated.pBeta)
    (hinputLow : input ≤ fabricated.nThreshold)
    (hpOn : fabricated.pThreshold < supply - input)
    (hdc : LoadedInverterDC fabricated supply input output) :
    output = supply := by
  rcases hdc with ⟨houtput0, houtput1, hkcl⟩
  have hnzero :
      mos1ForwardCurrent
        { polarity := .nmos, threshold := fabricated.nThreshold,
          beta := fabricated.nBeta, lambda := 0 }
        input output = 0 := by
    simp [mos1ForwardCurrent, hinputLow]
  rw [hnzero] at hkcl
  have hpzero :=
    (mos1ForwardCurrent_eq_zero_iff .pmos fabricated.pThreshold
      fabricated.pBeta (supply - input) (supply - output)
      hbeta hpOn (by linarith)).mp hkcl.symm
  linarith

/-- A high-band input forces the unique DC output to ground. -/
theorem loadedInverter_dc_high
    {fabricated : LoadedInverterInstance} {supply input output : ℝ}
    (hbeta : 0 < fabricated.nBeta)
    (hpOff : supply - input ≤ fabricated.pThreshold)
    (hnOn : fabricated.nThreshold < input)
    (hdc : LoadedInverterDC fabricated supply input output) :
    output = 0 := by
  rcases hdc with ⟨houtput0, houtput1, hkcl⟩
  have hpzero :
      mos1ForwardCurrent
        { polarity := .pmos, threshold := fabricated.pThreshold,
          beta := fabricated.pBeta, lambda := 0 }
        (supply - input) (supply - output) = 0 := by
    simp [mos1ForwardCurrent, hpOff]
  rw [hpzero] at hkcl
  exact
    (mos1ForwardCurrent_eq_zero_iff .nmos fabricated.nThreshold
      fabricated.nBeta input output hbeta hnOn houtput0).mp hkcl

/-- The nonlinear DC equation has an operating point for every input in the
supply interval. This is a non-vacuity theorem, independent of any numerical
Newton convergence claim. -/
theorem loadedInverter_dc_exists
    (fabricated : LoadedInverterInstance) {supply input : ℝ}
    (hsupply : 0 ≤ supply)
    (hinput0 : 0 ≤ input) (hinput1 : input ≤ supply)
    (hnbeta : 0 ≤ fabricated.nBeta)
    (hpbeta : 0 ≤ fabricated.pBeta) :
    ∃ output, LoadedInverterDC fabricated supply input output := by
  let residual : ℝ → ℝ := fun output =>
    mos1EnvelopeCurrent fabricated.nBeta fabricated.nThreshold input output -
      mos1EnvelopeCurrent fabricated.pBeta fabricated.pThreshold
        (supply - input) (supply - output)
  have hcontinuous : Continuous residual := by
    apply Continuous.sub
    · exact mos1EnvelopeCurrent_continuous _ _ _
    · exact (mos1EnvelopeCurrent_continuous _ _ _).comp
        (continuous_const.sub continuous_id)
  have hn0 :
      mos1EnvelopeCurrent fabricated.nBeta fabricated.nThreshold input 0 = 0 := by
    simp [mos1EnvelopeCurrent, railCurrent, clampedDrop]
  have hp0 :
      mos1EnvelopeCurrent fabricated.pBeta fabricated.pThreshold
        (supply - input) 0 = 0 := by
    simp [mos1EnvelopeCurrent, railCurrent, clampedDrop]
  have hpNonnegative :
      0 ≤ mos1EnvelopeCurrent fabricated.pBeta fabricated.pThreshold
        (supply - input) supply := by
    apply railCurrent_nonneg hpbeta
    exact le_max_left _ _
  have hnNonnegative :
      0 ≤ mos1EnvelopeCurrent fabricated.nBeta fabricated.nThreshold
        input supply := by
    apply railCurrent_nonneg hnbeta
    exact le_max_left _ _
  have hleft : residual 0 ≤ 0 := by
    simpa [residual, hn0] using neg_nonpos.mpr hpNonnegative
  have hright : 0 ≤ residual supply := by
    simpa [residual, hp0] using hnNonnegative
  have hzero :
      (0 : ℝ) ∈ Set.Icc (residual 0) (residual supply) :=
    ⟨hleft, hright⟩
  obtain ⟨output, hbounds, hresidual⟩ :=
    (intermediate_value_Icc hsupply hcontinuous.continuousOn hzero)
  refine ⟨output, hbounds.1, hbounds.2, ?_⟩
  dsimp [residual] at hresidual
  have hnExact :
      mos1EnvelopeCurrent fabricated.nBeta fabricated.nThreshold
          input output =
        mos1ForwardCurrent
          { polarity := .nmos, threshold := fabricated.nThreshold,
            beta := fabricated.nBeta, lambda := 0 } input output :=
    mos1EnvelopeCurrent_eq_mos1 (polarity := .nmos) hnbeta hbounds.1
  have hpExact :
      mos1EnvelopeCurrent fabricated.pBeta fabricated.pThreshold
          (supply - input) (supply - output) =
        mos1ForwardCurrent
          { polarity := .pmos, threshold := fabricated.pThreshold,
            beta := fabricated.pBeta, lambda := 0 }
          (supply - input) (supply - output) :=
    mos1EnvelopeCurrent_eq_mos1 (polarity := .pmos) hpbeta
      (show 0 ≤ supply - output by linarith [hbounds.2])
  rw [hnExact, hpExact] at hresidual
  linarith

/-- Current drawn from the positive rail through the PMOS channel. -/
noncomputable def loadedInverterSupplyCurrent
    (fabricated : LoadedInverterInstance)
    (supply input output : ℝ) : ℝ :=
  mos1ForwardCurrent
    { polarity := .pmos, threshold := fabricated.pThreshold,
      beta := fabricated.pBeta, lambda := 0 }
    (supply - input) (supply - output)

/-- Static CMOS draws no channel current in either proved rail state. -/
theorem loadedInverter_static_power_zero
    {fabricated : LoadedInverterInstance} {supply : ℝ} {input : Bool}
    (hsupply : 0 < supply)
    (hnt0 : 0 < fabricated.nThreshold)
    (hnt : fabricated.nThreshold < supply)
    (hpt0 : 0 < fabricated.pThreshold)
    (hpt : fabricated.pThreshold < supply)
    (hnbeta : 0 < fabricated.nBeta)
    (hpbeta : 0 < fabricated.pBeta)
    {output : ℝ}
    (hdc :
      LoadedInverterDC fabricated supply
        (if input then supply else 0) output) :
    loadedInverterSupplyCurrent fabricated supply
      (if input then supply else 0) output = 0 := by
  cases input with
  | false =>
      simp only [Bool.false_eq_true, if_false] at hdc ⊢
      have hout := loadedInverter_dc_low hpbeta
        (show (0 : ℝ) ≤ fabricated.nThreshold by linarith)
        (by simpa using hpt) hdc
      subst output
      unfold loadedInverterSupplyCurrent
      simpa using
        (mos1ForwardCurrent_eq_zero_iff .pmos fabricated.pThreshold
          fabricated.pBeta supply 0 hpbeta hpt (by norm_num)).mpr rfl
  | true =>
      simp only [if_true] at hdc ⊢
      have hout := loadedInverter_dc_high hnbeta
        (show supply - supply ≤ fabricated.pThreshold by linarith [hpt0])
        hnt (by simpa using hdc)
      subst output
      simp [loadedInverterSupplyCurrent, mos1ForwardCurrent,
        le_of_lt hpt0]

/-! ## Loaded transient behavior -/

def LoadedInverterEnvironment.inputVoltage
    (environment : LoadedInverterEnvironment) : ℝ :=
  if environment.input then environment.supply else 0

noncomputable def loadedInverterNOverdrive
    (world : LoadedInverterWorld) : ℝ :=
  world.environment.supply - world.fabricated.nThreshold

noncomputable def loadedInverterPOverdrive
    (world : LoadedInverterWorld) : ℝ :=
  world.environment.supply - world.fabricated.pThreshold

/-- Globally Lipschitz rail-driven vector field. Inside the supply domain this
is definitionally tied to the MOS1 triode/saturation current by
`mos1EnvelopeCurrent_eq_mos1`. -/
noncomputable def loadedInverterField
    (world : LoadedInverterWorld) (output : ℝ) : ℝ :=
  if world.environment.input then
    -railCurrent world.fabricated.nBeta
      (loadedInverterNOverdrive world) output /
        world.fabricated.loadCapacitance
  else
    railCurrent world.fabricated.pBeta
      (loadedInverterPOverdrive world)
      (world.environment.supply - output) /
        world.fabricated.loadCapacitance

noncomputable def loadedInverterFieldBound
    (world : LoadedInverterWorld) : ℝ :=
  if world.environment.input then
    world.fabricated.nBeta *
      loadedInverterNOverdrive world ^ 2 /
      (2 * world.fabricated.loadCapacitance)
  else
    world.fabricated.pBeta *
      loadedInverterPOverdrive world ^ 2 /
      (2 * world.fabricated.loadCapacitance)

noncomputable def loadedInverterFieldLipschitz
    (world : LoadedInverterWorld) : ℝ :=
  if world.environment.input then
    world.fabricated.nBeta * loadedInverterNOverdrive world /
      world.fabricated.loadCapacitance
  else
    world.fabricated.pBeta * loadedInverterPOverdrive world /
      world.fabricated.loadCapacitance

private theorem lipschitz_div_pos
    {f : ℝ → ℝ} {coefficient divisor : ℝ}
    (hcoefficient : 0 ≤ coefficient) (hdivisor : 0 < divisor)
    (hf : LipschitzWith coefficient.toNNReal f) :
    LipschitzWith (coefficient / divisor).toNNReal
      (fun value => f value / divisor) := by
  apply LipschitzWith.of_dist_le_mul
  intro left right
  have hbound := hf.dist_le_mul left right
  simp only [Real.dist_eq] at hbound ⊢
  rw [Real.coe_toNNReal coefficient hcoefficient] at hbound
  rw [Real.coe_toNNReal (coefficient / divisor)
      (div_nonneg hcoefficient hdivisor.le)]
  rw [show f left / divisor - f right / divisor =
    (f left - f right) / divisor by ring, abs_div,
    abs_of_pos hdivisor]
  calc
    |f left - f right| / divisor
        ≤ (coefficient * |left - right|) / divisor :=
      div_le_div_of_nonneg_right hbound hdivisor.le
    _ = coefficient / divisor * |left - right| := by ring

theorem loadedInverterField_lipschitz
    {world : LoadedInverterWorld}
    (hadmissible : LoadedInverterAdmissible world) :
    LipschitzWith (loadedInverterFieldLipschitz world).toNNReal
      (loadedInverterField world) := by
  rcases hadmissible with
    ⟨hnbeta, hpbeta, hcap, hnt0, hnt1, hpt0, hpt1,
      hinitial0, hinitial1, hhorizon⟩
  have hnOverdrive : 0 ≤ loadedInverterNOverdrive world := by
    unfold loadedInverterNOverdrive
    linarith
  have hpOverdrive : 0 ≤ loadedInverterPOverdrive world := by
    unfold loadedInverterPOverdrive
    linarith
  unfold loadedInverterField loadedInverterFieldLipschitz
  split
  next hinput =>
    have hrail :=
      railCurrent_lipschitz hnbeta.le hnOverdrive
    have hrail' :
        LipschitzWith
          (world.fabricated.nBeta *
            loadedInverterNOverdrive world).toNNReal
          (railCurrent world.fabricated.nBeta
            (loadedInverterNOverdrive world)) := by
      rw [Real.toNNReal_of_nonneg
        (mul_nonneg hnbeta.le hnOverdrive)]
      exact hrail
    have hscaled :=
      lipschitz_div_pos
        (mul_nonneg hnbeta.le hnOverdrive)
        hcap hrail'
    have hneg :
        LipschitzWith
          (world.fabricated.nBeta *
            loadedInverterNOverdrive world /
            world.fabricated.loadCapacitance).toNNReal
          (fun output =>
            -(railCurrent world.fabricated.nBeta
                (loadedInverterNOverdrive world) output /
              world.fabricated.loadCapacitance)) := by
      apply LipschitzWith.of_dist_le_mul
      intro left right
      simpa only [dist_neg_neg] using hscaled.dist_le_mul left right
    simpa [neg_div] using hneg
  next hinput =>
    have hrail :=
      railCurrent_lipschitz hpbeta.le hpOverdrive
    have hrail' :
        LipschitzWith
          (world.fabricated.pBeta *
            loadedInverterPOverdrive world).toNNReal
          (railCurrent world.fabricated.pBeta
            (loadedInverterPOverdrive world)) := by
      rw [Real.toNNReal_of_nonneg
        (mul_nonneg hpbeta.le hpOverdrive)]
      exact hrail
    have hreflection :
        LipschitzWith 1
          (fun output : ℝ => world.environment.supply - output) := by
      simpa using
        (LipschitzWith.const world.environment.supply).sub
          LipschitzWith.id
    have hcomposed := hrail'.comp hreflection
    have hcomposed' :
        LipschitzWith
          (world.fabricated.pBeta *
            loadedInverterPOverdrive world).toNNReal
          (fun output =>
            railCurrent world.fabricated.pBeta
              (loadedInverterPOverdrive world)
              (world.environment.supply - output)) := by
      intro left right
      simpa only [mul_one, Function.comp_apply] using hcomposed left right
    have hscaled :=
      lipschitz_div_pos
        (mul_nonneg hpbeta.le hpOverdrive)
        hcap hcomposed'
    simpa using hscaled

theorem loadedInverterField_norm_le
    {world : LoadedInverterWorld}
    (hadmissible : LoadedInverterAdmissible world) (output : ℝ) :
    ‖loadedInverterField world output‖ ≤
      loadedInverterFieldBound world := by
  rcases hadmissible with
    ⟨hnbeta, hpbeta, hcap, hnt0, hnt1, hpt0, hpt1,
      hinitial0, hinitial1, hhorizon⟩
  have hnOverdrive : 0 ≤ loadedInverterNOverdrive world := by
    unfold loadedInverterNOverdrive
    linarith
  have hpOverdrive : 0 ≤ loadedInverterPOverdrive world := by
    unfold loadedInverterPOverdrive
    linarith
  unfold loadedInverterField loadedInverterFieldBound
  split
  next hinput =>
    have hnonnegative :=
      railCurrent_nonneg (drop := output) hnbeta.le hnOverdrive
    have hupper :=
      railCurrent_le (drop := output) hnbeta.le hnOverdrive
    rw [Real.norm_eq_abs, abs_div, abs_neg,
      abs_of_nonneg hnonnegative,
      abs_of_pos hcap]
    calc
      railCurrent world.fabricated.nBeta
          (loadedInverterNOverdrive world) output /
          world.fabricated.loadCapacitance
        ≤ (world.fabricated.nBeta *
            loadedInverterNOverdrive world ^ 2 / 2) /
            world.fabricated.loadCapacitance :=
          div_le_div_of_nonneg_right hupper hcap.le
      _ = world.fabricated.nBeta *
          loadedInverterNOverdrive world ^ 2 /
          (2 * world.fabricated.loadCapacitance) := by ring
  next hinput =>
    have hnonnegative :=
      railCurrent_nonneg
        (drop := world.environment.supply - output)
        hpbeta.le hpOverdrive
    have hupper :=
      railCurrent_le
        (drop := world.environment.supply - output)
        hpbeta.le hpOverdrive
    rw [Real.norm_eq_abs, abs_div, abs_of_nonneg hnonnegative,
      abs_of_pos hcap]
    calc
      railCurrent world.fabricated.pBeta
          (loadedInverterPOverdrive world)
          (world.environment.supply - output) /
          world.fabricated.loadCapacitance
        ≤ (world.fabricated.pBeta *
            loadedInverterPOverdrive world ^ 2 / 2) /
            world.fabricated.loadCapacitance :=
          div_le_div_of_nonneg_right hupper hcap.le
      _ = world.fabricated.pBeta *
          loadedInverterPOverdrive world ^ 2 /
          (2 * world.fabricated.loadCapacitance) := by ring

theorem loadedInverterFieldBound_nonneg
    {world : LoadedInverterWorld}
    (hadmissible : LoadedInverterAdmissible world) :
    0 ≤ loadedInverterFieldBound world := by
  have := loadedInverterField_norm_le hadmissible 0
  exact (norm_nonneg _).trans this

/-- Observable output voltage of the loaded inverter. -/
structure LoadedInverterBoundary where
  outputVoltage : DenseTrace ℝ

/-- Pointwise ODE behavior used for existence, uniqueness, and ordinary
inverter runs without discrete events. -/
noncomputable def LoadedInverterSmoothBehavior :
    Behavior LoadedInverterWorld LoadedInverterBoundary Unit :=
  fun world boundary _internal =>
    boundary.outputVoltage 0 = world.environment.initialVoltage ∧
    ∀ time ∈ Icc 0 world.environment.horizon,
      HasDerivWithinAt boundary.outputVoltage
        (loadedInverterField world (boundary.outputVoltage time))
        (Icc 0 world.environment.horizon) time

/-- Finite-horizon existence follows from Picard-Lindelöf for the proved
global current bound and Lipschitz constant. -/
theorem loadedInverter_smooth_realizable :
    RealizableUnder LoadedInverterSmoothBehavior
      LoadedInverterAdmissible := by
  intro world hadmissible
  rcases hadmissible with
    ⟨hnbeta, hpbeta, hcap, hnt0, hnt1, hpt0, hpt1,
      hinitial0, hinitial1, hhorizon⟩
  have hadmissible' : LoadedInverterAdmissible world :=
    ⟨hnbeta, hpbeta, hcap, hnt0, hnt1, hpt0, hpt1,
      hinitial0, hinitial1, hhorizon⟩
  let L : NNReal := (loadedInverterFieldBound world).toNNReal
  let K : NNReal := (loadedInverterFieldLipschitz world).toNNReal
  let H : NNReal := world.environment.horizon.toNNReal
  let a : NNReal := L * H
  let t0 : Icc (0 : ℝ) world.environment.horizon :=
    ⟨0, le_rfl, hhorizon⟩
  have hpicard :
      IsPicardLindelof
        (fun _time => loadedInverterField world)
        t0 world.environment.initialVoltage a 0 L K := by
    apply IsPicardLindelof.of_time_independent
    · intro output _houtput
      have hbound :=
        loadedInverterField_norm_le hadmissible' output
      simpa [L, Real.coe_toNNReal _ 
        (loadedInverterFieldBound_nonneg hadmissible')] using hbound
    · exact
        (loadedInverterField_lipschitz hadmissible').lipschitzOnWith
    · dsimp [a, L, H, t0]
      simp [max_eq_left hhorizon]
  obtain ⟨trace, hinitial, hderivative⟩ :=
    hpicard.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨⟨trace⟩, (), hinitial, hderivative⟩

theorem loadedInverterSmooth_continuousOn
    {world : LoadedInverterWorld} {boundary : LoadedInverterBoundary}
    (hbehavior : LoadedInverterSmoothBehavior world boundary ()) :
    ContinuousOn boundary.outputVoltage
      (Icc 0 world.environment.horizon) :=
  HasDerivWithinAt.continuousOn hbehavior.2

theorem loadedInverterSmooth_derivRight
    {world : LoadedInverterWorld} {boundary : LoadedInverterBoundary}
    (hbehavior : LoadedInverterSmoothBehavior world boundary ())
    {time : ℝ} (htime : time ∈ Ico 0 world.environment.horizon) :
    HasDerivWithinAt boundary.outputVoltage
      (loadedInverterField world (boundary.outputVoltage time))
      (Ici time) time :=
  (hbehavior.2 time (Ico_subset_Icc_self htime)).mono_of_mem_nhdsWithin
    (Icc_mem_nhdsGE_of_mem htime)

theorem loadedInverterField_nonneg_of_low
    {world : LoadedInverterWorld}
    (hadmissible : LoadedInverterAdmissible world)
    (hinput : world.environment.input = false) (output : ℝ) :
    0 ≤ loadedInverterField world output := by
  rw [loadedInverterField, if_neg (by simpa using hinput)]
  exact div_nonneg
    (railCurrent_nonneg hadmissible.2.1.le
      (by
        unfold loadedInverterPOverdrive
        linarith [hadmissible.2.2.2.2.2.2.1]))
    hadmissible.2.2.1.le

theorem loadedInverterField_nonpos_of_high
    {world : LoadedInverterWorld}
    (hadmissible : LoadedInverterAdmissible world)
    (hinput : world.environment.input = true) (output : ℝ) :
    loadedInverterField world output ≤ 0 := by
  rw [loadedInverterField, if_pos hinput]
  exact div_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr
      (railCurrent_nonneg hadmissible.1.le
        (by
          unfold loadedInverterNOverdrive
          linarith [hadmissible.2.2.2.2.1])))
    hadmissible.2.2.1.le

theorem loadedInverterField_zero_above
    {world : LoadedInverterWorld}
    (hinput : world.environment.input = false)
    {output : ℝ} (habove : world.environment.supply ≤ output) :
    loadedInverterField world output = 0 := by
  rw [loadedInverterField, if_neg (by simpa using hinput)]
  unfold railCurrent
  rw [show clampedDrop (loadedInverterPOverdrive world)
      (world.environment.supply - output) = 0 by
        apply clampedDrop_eq_zero
        linarith]
  simp [railCurrent]

theorem loadedInverterField_zero_below
    {world : LoadedInverterWorld}
    (hinput : world.environment.input = true)
    {output : ℝ} (hbelow : output ≤ 0) :
    loadedInverterField world output = 0 := by
  rw [loadedInverterField, if_pos hinput]
  unfold railCurrent
  rw [show clampedDrop (loadedInverterNOverdrive world) output = 0 by
    exact clampedDrop_eq_zero hbelow]
  simp [railCurrent]

theorem loadedInverter_monotone_charging
    {world : LoadedInverterWorld} {boundary : LoadedInverterBoundary}
    (hadmissible : LoadedInverterAdmissible world)
    (hinput : world.environment.input = false)
    (hbehavior : LoadedInverterSmoothBehavior world boundary ()) :
    MonotoneOn boundary.outputVoltage
      (Icc 0 world.environment.horizon) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg
    (convex_Icc (0 : ℝ) world.environment.horizon)
    (loadedInverterSmooth_continuousOn hbehavior)
  · intro time htime
    exact (hbehavior.2 time (interior_subset htime)).mono interior_subset
  · intro time _htime
    exact loadedInverterField_nonneg_of_low hadmissible hinput _

theorem loadedInverter_antitone_discharging
    {world : LoadedInverterWorld} {boundary : LoadedInverterBoundary}
    (hadmissible : LoadedInverterAdmissible world)
    (hinput : world.environment.input = true)
    (hbehavior : LoadedInverterSmoothBehavior world boundary ()) :
    AntitoneOn boundary.outputVoltage
      (Icc 0 world.environment.horizon) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos
    (convex_Icc (0 : ℝ) world.environment.horizon)
    (loadedInverterSmooth_continuousOn hbehavior)
  · intro time htime
    exact (hbehavior.2 time (interior_subset htime)).mono interior_subset
  · intro time _htime
    exact loadedInverterField_nonpos_of_high hadmissible hinput _

/-- The native scalar DAE is the capacitor charge derivative balanced by the
globally extended rail current. -/
noncomputable def loadedInverterDAE :
    ScalarDAE LoadedInverterWorld where
  residual world _time output derivative :=
    derivative = loadedInverterField world output

/-- Absolutely-continuous, almost-everywhere DAE behavior. -/
noncomputable def LoadedInverterPhysicalBehavior :
    Behavior LoadedInverterWorld LoadedInverterBoundary Unit :=
  fun world boundary _internal =>
    boundary.outputVoltage 0 = world.environment.initialVoltage ∧
    loadedInverterDAE.ACBehavesOn world world.environment.horizon
      boundary.outputVoltage

theorem loadedInverter_smooth_is_physical
    {world : LoadedInverterWorld} {boundary : LoadedInverterBoundary}
    (hadmissible : LoadedInverterAdmissible world)
    (hbehavior : LoadedInverterSmoothBehavior world boundary ()) :
    LoadedInverterPhysicalBehavior world boundary () := by
  refine ⟨hbehavior.1, hadmissible.2.2.2.2.2.2.2.2.2, ?_, ?_⟩
  · let L : NNReal := (loadedInverterFieldBound world).toNNReal
    have hbound :
        ∀ time ∈ Icc 0 world.environment.horizon,
          ‖loadedInverterField world (boundary.outputVoltage time)‖₊ ≤ L := by
      intro time _htime
      rw [← NNReal.coe_le_coe, coe_nnnorm]
      simpa [L, Real.coe_toNNReal _
        (loadedInverterFieldBound_nonneg hadmissible)] using
        loadedInverterField_norm_le hadmissible
          (boundary.outputVoltage time)
    have hlipschitz :=
      Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le
        (convex_Icc (0 : ℝ) world.environment.horizon)
        hbehavior.2 hbound
    apply LipschitzOnWith.absolutelyContinuousOnInterval
    rw [Set.uIcc_of_le hadmissible.2.2.2.2.2.2.2.2.2]
    exact hlipschitz
  · rw [Set.uIcc_of_le hadmissible.2.2.2.2.2.2.2.2.2]
    rw [← MeasureTheory.Measure.restrict_congr_set
      -- Endpoints are null, so pointwise within-derivatives suffice.
      (MeasureTheory.Ioo_ae_eq_Icc :
        Ioo (0 : ℝ) world.environment.horizon =ᵐ[
          MeasureTheory.volume]
        Icc 0 world.environment.horizon)]
    exact MeasureTheory.ae_restrict_of_forall_mem
      measurableSet_Ioo fun time htime => by
        refine ⟨loadedInverterField world
          (boundary.outputVoltage time), ?_, rfl⟩
        exact
          (hbehavior.2 time (Ioo_subset_Icc_self htime)).hasDerivAt
            (Icc_mem_nhds htime.1 htime.2)

theorem loadedInverter_physical_realizable :
    RealizableUnder LoadedInverterPhysicalBehavior
      LoadedInverterAdmissible := by
  intro world hadmissible
  obtain ⟨boundary, internal, hbehavior⟩ :=
    loadedInverter_smooth_realizable world hadmissible
  exact ⟨boundary, internal,
    loadedInverter_smooth_is_physical hadmissible hbehavior⟩

/-- Public loaded-inverter behavior. The first conjunct is the physical,
absolutely-continuous a.e. DAE denotation; the second is the certified smooth
capability used by the current settling automation. -/
noncomputable def LoadedInverterBehavior :
    Behavior LoadedInverterWorld LoadedInverterBoundary Unit :=
  fun world boundary internal =>
    LoadedInverterPhysicalBehavior world boundary internal ∧
      LoadedInverterSmoothBehavior world boundary internal

theorem loadedInverter_realizable :
    RealizableUnder LoadedInverterBehavior
      LoadedInverterAdmissible := by
  intro world hadmissible
  obtain ⟨boundary, internal, hsmooth⟩ :=
    loadedInverter_smooth_realizable world hadmissible
  exact ⟨boundary, internal,
    loadedInverter_smooth_is_physical hadmissible hsmooth, hsmooth⟩

private theorem eq_endpoints_of_zero_derivative
    {trace : ℝ → ℝ} {left right : ℝ} (hleftRight : left ≤ right)
    (hderivative :
      ∀ time ∈ Icc left right,
        HasDerivWithinAt trace 0 (Icc left right) time) :
    trace left = trace right := by
  have hnorm :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (C := 0) (f' := fun _time => 0)
      hderivative (fun _time _htime => by norm_num)
      (convex_Icc left right)
      (show left ∈ Icc left right from ⟨le_rfl, hleftRight⟩)
      (show right ∈ Icc left right from ⟨hleftRight, le_rfl⟩)
  have hzero : ‖trace right - trace left‖ = 0 :=
    le_antisymm (by simpa using hnorm) (norm_nonneg _)
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero) |>.symm

/-- The compact-model validity domain used by the loaded-inverter theorems. -/
def LoadedInverterValidityDomain
    (world : LoadedInverterWorld)
    (boundary : LoadedInverterBoundary) (_internal : Unit) : Prop :=
  ∀ time ∈ Icc 0 world.environment.horizon,
    0 ≤ boundary.outputVoltage time ∧
      boundary.outputVoltage time ≤ world.environment.supply

theorem loadedInverter_stays_in_validity_domain :
    StaysWithinValidityDomain
      LoadedInverterSmoothBehavior LoadedInverterAdmissible
      LoadedInverterValidityDomain := by
  intro world boundary _internal hadmissible hbehavior
  intro time htime
  cases hinput : world.environment.input with
  | false =>
      have hmonotone :=
        loadedInverter_monotone_charging hadmissible hinput hbehavior
      have hlower :
          0 ≤ boundary.outputVoltage time := by
        have hstart :
            boundary.outputVoltage 0 ≤ boundary.outputVoltage time :=
          hmonotone (by
            exact ⟨le_rfl, hadmissible.2.2.2.2.2.2.2.2.2⟩)
            htime htime.1
        rw [hbehavior.1] at hstart
        exact hadmissible.2.2.2.2.2.2.2.1.trans hstart
      refine ⟨hlower, ?_⟩
      by_contra habove
      have habove' :
          world.environment.supply <
            boundary.outputVoltage time :=
        lt_of_not_ge habove
      have hcontinuous :
          ContinuousOn boundary.outputVoltage (Icc 0 time) :=
        (loadedInverterSmooth_continuousOn hbehavior).mono
          (fun point hpoint => ⟨hpoint.1, hpoint.2.trans htime.2⟩)
      have hsupplyBetween :
          world.environment.supply ∈
            Icc (boundary.outputVoltage 0)
              (boundary.outputVoltage time) := by
        rw [hbehavior.1]
        exact ⟨hadmissible.2.2.2.2.2.2.2.2.1, habove'.le⟩
      obtain ⟨crossing, hcrossing, hcrossingVoltage⟩ :=
        intermediate_value_Icc htime.1 hcontinuous hsupplyBetween
      have hzeroDerivative :
          ∀ point ∈ Icc crossing time,
            HasDerivWithinAt boundary.outputVoltage 0
              (Icc crossing time) point := by
        intro point hpoint
        have hpointWhole :
            point ∈ Icc 0 world.environment.horizon :=
          ⟨hcrossing.1.trans hpoint.1,
            hpoint.2.trans htime.2⟩
        have hcrossingWhole :
            crossing ∈ Icc 0 world.environment.horizon :=
          ⟨hcrossing.1, hcrossing.2.trans htime.2⟩
        have habovePoint :
            world.environment.supply ≤
              boundary.outputVoltage point := by
          rw [← hcrossingVoltage]
          exact hmonotone hcrossingWhole hpointWhole hpoint.1
        exact
          ((hbehavior.2 point hpointWhole).mono
              (fun candidate hcandidate =>
                ⟨hcrossingWhole.1.trans hcandidate.1,
                  hcandidate.2.trans htime.2⟩)).congr_deriv
            (loadedInverterField_zero_above hinput habovePoint)
      have hconstant :=
        eq_endpoints_of_zero_derivative hcrossing.2 hzeroDerivative
      rw [hcrossingVoltage] at hconstant
      linarith
  | true =>
      have hantitone :=
        loadedInverter_antitone_discharging hadmissible hinput hbehavior
      have hupper :
          boundary.outputVoltage time ≤ world.environment.supply := by
        have hstart :
            boundary.outputVoltage time ≤ boundary.outputVoltage 0 :=
          hantitone (by
            exact ⟨le_rfl, hadmissible.2.2.2.2.2.2.2.2.2⟩)
            htime htime.1
        rw [hbehavior.1] at hstart
        exact hstart.trans hadmissible.2.2.2.2.2.2.2.2.1
      refine ⟨?_, hupper⟩
      by_contra hbelow
      have hbelow' : boundary.outputVoltage time < 0 :=
        lt_of_not_ge hbelow
      have hcontinuous :
          ContinuousOn boundary.outputVoltage (Icc 0 time) :=
        (loadedInverterSmooth_continuousOn hbehavior).mono
          (fun point hpoint => ⟨hpoint.1, hpoint.2.trans htime.2⟩)
      have hzeroBetween :
          (0 : ℝ) ∈
            Icc (boundary.outputVoltage time)
              (boundary.outputVoltage 0) := by
        rw [hbehavior.1]
        exact ⟨hbelow'.le, hadmissible.2.2.2.2.2.2.2.1⟩
      obtain ⟨crossing, hcrossing, hcrossingVoltage⟩ :=
        intermediate_value_Icc' htime.1 hcontinuous hzeroBetween
      have hzeroDerivative :
          ∀ point ∈ Icc crossing time,
            HasDerivWithinAt boundary.outputVoltage 0
              (Icc crossing time) point := by
        intro point hpoint
        have hpointWhole :
            point ∈ Icc 0 world.environment.horizon :=
          ⟨hcrossing.1.trans hpoint.1,
            hpoint.2.trans htime.2⟩
        have hcrossingWhole :
            crossing ∈ Icc 0 world.environment.horizon :=
          ⟨hcrossing.1, hcrossing.2.trans htime.2⟩
        have hbelowPoint :
            boundary.outputVoltage point ≤ 0 := by
          rw [← hcrossingVoltage]
          exact hantitone hcrossingWhole hpointWhole hpoint.1
        exact
          ((hbehavior.2 point hpointWhole).mono
              (fun candidate hcandidate =>
                ⟨hcrossingWhole.1.trans hcandidate.1,
                  hcandidate.2.trans htime.2⟩)).congr_deriv
            (loadedInverterField_zero_below hinput hbelowPoint)
      have hconstant :=
        eq_endpoints_of_zero_derivative hcrossing.2 hzeroDerivative
      rw [hcrossingVoltage] at hconstant
      linarith

theorem loadedInverter_no_overshoot
    {world : LoadedInverterWorld} {boundary : LoadedInverterBoundary}
    (hadmissible : LoadedInverterAdmissible world)
    (hbehavior : LoadedInverterSmoothBehavior world boundary ()) :
    LoadedInverterValidityDomain world boundary () :=
  loadedInverter_stays_in_validity_domain
    world boundary () hadmissible hbehavior

theorem railCurrent_ge_linear
    {beta overdrive supply drop : ℝ}
    (hbeta : 0 ≤ beta) (hoverdrive0 : 0 ≤ overdrive)
    (hoverdriveSupply : overdrive ≤ supply) (hsupply : 0 < supply)
    (hdrop0 : 0 ≤ drop) (hdropSupply : drop ≤ supply) :
    beta * overdrive ^ 2 / (2 * supply) * drop ≤
      railCurrent beta overdrive drop := by
  by_cases htriode : drop ≤ overdrive
  · rw [railCurrent, clampedDrop_eq_self hdrop0 htriode]
    have hscale : overdrive ^ 2 / supply ≤ overdrive := by
      apply (div_le_iff₀ hsupply).mpr
      simpa [pow_two] using
        mul_le_mul_of_nonneg_left hoverdriveSupply hoverdrive0
    have hscaleHalf :
        overdrive ^ 2 / (2 * supply) ≤ overdrive / 2 := by
      calc
        overdrive ^ 2 / (2 * supply)
            = (overdrive ^ 2 / supply) / 2 := by ring
        _ ≤ overdrive / 2 := by gcongr
    have hshape :
        overdrive ^ 2 / (2 * supply) * drop ≤
          overdrive * drop - drop ^ 2 / 2 := by
      calc
        _ ≤ (overdrive / 2) * drop :=
          mul_le_mul_of_nonneg_right hscaleHalf hdrop0
        _ ≤ overdrive * drop - drop ^ 2 / 2 := by
          nlinarith [mul_nonneg hdrop0
            (show 0 ≤ overdrive - drop by linarith)]
    have hscaled := mul_le_mul_of_nonneg_left hshape hbeta
    calc
      beta * overdrive ^ 2 / (2 * supply) * drop =
          beta * (overdrive ^ 2 / (2 * supply) * drop) := by ring
      _ ≤ beta * (overdrive * drop - drop ^ 2 / 2) := hscaled
  · have hoverdriveDrop : overdrive ≤ drop := le_of_not_ge htriode
    rw [railCurrent,
      clampedDrop_eq_overdrive hoverdrive0 hoverdriveDrop]
    have hratio : drop / supply ≤ 1 :=
      (div_le_one hsupply).mpr hdropSupply
    have hnonnegative : 0 ≤ beta * overdrive ^ 2 / 2 := by
      positivity
    calc
      beta * overdrive ^ 2 / (2 * supply) * drop
          = (beta * overdrive ^ 2 / 2) * (drop / supply) := by
            field_simp [ne_of_gt hsupply]
      _ ≤ (beta * overdrive ^ 2 / 2) * 1 :=
        mul_le_mul_of_nonneg_left hratio hnonnegative
      _ = beta * (overdrive * overdrive - overdrive ^ 2 / 2) := by
        ring

noncomputable def loadedInverterDecayRate
    (world : LoadedInverterWorld) : ℝ :=
  if world.environment.input then
    world.fabricated.nBeta * loadedInverterNOverdrive world ^ 2 /
      (2 * world.fabricated.loadCapacitance *
        world.environment.supply)
  else
    world.fabricated.pBeta * loadedInverterPOverdrive world ^ 2 /
      (2 * world.fabricated.loadCapacitance *
        world.environment.supply)

theorem loadedInverterDecayRate_pos
    {world : LoadedInverterWorld}
    (hadmissible : LoadedInverterAdmissible world) :
    0 < loadedInverterDecayRate world := by
  have hsupply : 0 < world.environment.supply := by
    linarith [hadmissible.2.2.2.1, hadmissible.2.2.2.2.1]
  have hnOverdrive : 0 < loadedInverterNOverdrive world := by
    unfold loadedInverterNOverdrive
    linarith [hadmissible.2.2.2.2.1]
  have hpOverdrive : 0 < loadedInverterPOverdrive world := by
    unfold loadedInverterPOverdrive
    linarith [hadmissible.2.2.2.2.2.2.1]
  unfold loadedInverterDecayRate
  split
  · exact div_pos
      (mul_pos hadmissible.1 (sq_pos_of_pos hnOverdrive))
      (mul_pos (mul_pos (by norm_num) hadmissible.2.2.1) hsupply)
  · exact div_pos
      (mul_pos hadmissible.2.1 (sq_pos_of_pos hpOverdrive))
      (mul_pos (mul_pos (by norm_num) hadmissible.2.2.1) hsupply)

noncomputable def loadedInverterError
    (world : LoadedInverterWorld) (output : ℝ) : ℝ :=
  if world.environment.input then output
  else world.environment.supply - output

noncomputable def loadedInverterErrorTrace
    (world : LoadedInverterWorld) (boundary : LoadedInverterBoundary) :
    DenseTrace ℝ :=
  fun time =>
    loadedInverterError world (boundary.outputVoltage time)

noncomputable def loadedInverterInitialError
    (world : LoadedInverterWorld) : ℝ :=
  loadedInverterError world world.environment.initialVoltage

noncomputable def loadedInverterErrorDerivative
    (world : LoadedInverterWorld) (output : ℝ) : ℝ :=
  if world.environment.input then loadedInverterField world output
  else -loadedInverterField world output

theorem loadedInverterError_derivRight
    {world : LoadedInverterWorld} {boundary : LoadedInverterBoundary}
    (hbehavior : LoadedInverterSmoothBehavior world boundary ())
    {time : ℝ} (htime : time ∈ Ico 0 world.environment.horizon) :
    HasDerivWithinAt (loadedInverterErrorTrace world boundary)
      (loadedInverterErrorDerivative world
        (boundary.outputVoltage time))
      (Ici time) time := by
  have houtput :=
    loadedInverterSmooth_derivRight hbehavior htime
  unfold loadedInverterErrorTrace loadedInverterError
    loadedInverterErrorDerivative
  split
  · exact houtput
  · exact houtput.const_sub world.environment.supply

theorem loadedInverterError_nonneg
    {world : LoadedInverterWorld} {boundary : LoadedInverterBoundary}
    (hadmissible : LoadedInverterAdmissible world)
    (hbehavior : LoadedInverterSmoothBehavior world boundary ())
    {time : ℝ} (htime : time ∈ Icc 0 world.environment.horizon) :
    0 ≤ loadedInverterErrorTrace world boundary time := by
  have hdomain :=
    loadedInverter_no_overshoot hadmissible hbehavior time htime
  unfold loadedInverterErrorTrace loadedInverterError
  split
  · exact hdomain.1
  · linarith

theorem loadedInverterError_derivative_le
    {world : LoadedInverterWorld} {boundary : LoadedInverterBoundary}
    (hadmissible : LoadedInverterAdmissible world)
    (hbehavior : LoadedInverterSmoothBehavior world boundary ())
    {time : ℝ} (htime : time ∈ Icc 0 world.environment.horizon) :
    loadedInverterErrorDerivative world
        (boundary.outputVoltage time) ≤
      -loadedInverterDecayRate world *
        loadedInverterErrorTrace world boundary time := by
  have hdomain :=
    loadedInverter_no_overshoot hadmissible hbehavior time htime
  have hsupply : 0 < world.environment.supply := by
    linarith [hadmissible.2.2.2.1, hadmissible.2.2.2.2.1]
  cases hinput : world.environment.input with
  | false =>
      have hoverdrive0 : 0 ≤ loadedInverterPOverdrive world := by
        unfold loadedInverterPOverdrive
        linarith [hadmissible.2.2.2.2.2.2.1]
      have hoverdriveSupply :
          loadedInverterPOverdrive world ≤
            world.environment.supply := by
        unfold loadedInverterPOverdrive
        linarith [hadmissible.2.2.2.2.2.1]
      have hcurrent :=
        railCurrent_ge_linear hadmissible.2.1.le hoverdrive0
          hoverdriveSupply hsupply
          (show 0 ≤ world.environment.supply -
              boundary.outputVoltage time by linarith)
          (show world.environment.supply -
              boundary.outputVoltage time ≤
              world.environment.supply by linarith)
      simp only [loadedInverterErrorDerivative,
        loadedInverterErrorTrace, loadedInverterError,
        loadedInverterDecayRate, loadedInverterField,
        hinput, Bool.false_eq_true, if_false]
      have hcap := hadmissible.2.2.1
      have hdiv :=
        div_le_div_of_nonneg_right hcurrent hcap.le
      calc
        _ ≤ -((world.fabricated.pBeta *
              loadedInverterPOverdrive world ^ 2 /
              (2 * world.environment.supply) *
              (world.environment.supply -
                boundary.outputVoltage time)) /
              world.fabricated.loadCapacitance) :=
          neg_le_neg hdiv
        _ = -(world.fabricated.pBeta *
              loadedInverterPOverdrive world ^ 2 /
              (2 * world.fabricated.loadCapacitance *
                world.environment.supply)) *
              (world.environment.supply -
                boundary.outputVoltage time) := by ring
  | true =>
      have hoverdrive0 : 0 ≤ loadedInverterNOverdrive world := by
        unfold loadedInverterNOverdrive
        linarith [hadmissible.2.2.2.2.1]
      have hoverdriveSupply :
          loadedInverterNOverdrive world ≤
            world.environment.supply := by
        unfold loadedInverterNOverdrive
        linarith [hadmissible.2.2.2.1]
      have hcurrent :=
        railCurrent_ge_linear hadmissible.1.le hoverdrive0
          hoverdriveSupply hsupply hdomain.1 hdomain.2
      simp only [loadedInverterErrorDerivative,
        loadedInverterErrorTrace, loadedInverterError,
        loadedInverterDecayRate, loadedInverterField,
        hinput, if_true]
      have hcap := hadmissible.2.2.1
      have hdiv :=
        div_le_div_of_nonneg_right hcurrent hcap.le
      calc
        -railCurrent world.fabricated.nBeta
              (loadedInverterNOverdrive world)
              (boundary.outputVoltage time) /
              world.fabricated.loadCapacitance =
            -(railCurrent world.fabricated.nBeta
              (loadedInverterNOverdrive world)
              (boundary.outputVoltage time) /
              world.fabricated.loadCapacitance) := by ring
        _ ≤ -((world.fabricated.nBeta *
              loadedInverterNOverdrive world ^ 2 /
              (2 * world.environment.supply) *
              boundary.outputVoltage time) /
              world.fabricated.loadCapacitance) :=
          neg_le_neg hdiv
        _ = -(world.fabricated.nBeta *
              loadedInverterNOverdrive world ^ 2 /
              (2 * world.fabricated.loadCapacitance *
                world.environment.supply)) *
              boundary.outputVoltage time := by ring

theorem loadedInverter_error_exponential_bound
    {world : LoadedInverterWorld} {boundary : LoadedInverterBoundary}
    (hadmissible : LoadedInverterAdmissible world)
    (hbehavior : LoadedInverterSmoothBehavior world boundary ())
    {time : ℝ} (htime : time ∈ Icc 0 world.environment.horizon) :
    loadedInverterErrorTrace world boundary time ≤
      loadedInverterInitialError world *
        Real.exp (-loadedInverterDecayRate world * time) := by
  have hcontinuous :
      ContinuousOn (loadedInverterErrorTrace world boundary)
        (Icc 0 world.environment.horizon) := by
    unfold loadedInverterErrorTrace loadedInverterError
    split
    · exact loadedInverterSmooth_continuousOn hbehavior
    · exact continuousOn_const.sub
        (loadedInverterSmooth_continuousOn hbehavior)
  have hgronwall :=
    le_gronwallBound_of_liminf_deriv_right_le
      (f := loadedInverterErrorTrace world boundary)
      (f' := fun t => loadedInverterErrorDerivative world
        (boundary.outputVoltage t))
      (δ := loadedInverterInitialError world)
      (K := -loadedInverterDecayRate world) (ε := 0)
      hcontinuous
      (fun point hpoint _bound hstrict =>
        (loadedInverterError_derivRight hbehavior hpoint).liminf_right_slope_le
          hstrict)
      (by
        simpa [loadedInverterErrorTrace,
          loadedInverterInitialError, hbehavior.1])
      (fun point hpoint =>
        by simpa using
          loadedInverterError_derivative_le hadmissible hbehavior
            (Ico_subset_Icc_self hpoint))
      time htime
  rw [gronwallBound_ε0] at hgronwall
  simpa only [sub_zero] using hgronwall

theorem loadedInverter_settles_within
    {world : LoadedInverterWorld} {boundary : LoadedInverterBoundary}
    (hadmissible : LoadedInverterAdmissible world)
    (hbehavior : LoadedInverterSmoothBehavior world boundary ())
    {tolerance deadline : ℝ}
    (htolerance : 0 ≤ tolerance)
    (hdeadline0 : 0 ≤ deadline)
    (hdeadlineH : deadline ≤ world.environment.horizon)
    (hdeadline :
      loadedInverterInitialError world *
          Real.exp (-loadedInverterDecayRate world * deadline) ≤
        tolerance) :
    SettlesWithin boundary.outputVoltage
      (if world.environment.input then 0 else world.environment.supply)
      tolerance deadline world.environment.horizon := by
  refine ⟨htolerance, hdeadline0, hdeadlineH, ?_⟩
  intro time hdeadlineTime htimeH
  have htime : time ∈ Icc 0 world.environment.horizon :=
    ⟨hdeadline0.trans hdeadlineTime, htimeH⟩
  have herror :=
    loadedInverter_error_exponential_bound hadmissible hbehavior htime
  have hinitialNonnegative :
      0 ≤ loadedInverterInitialError world := by
    unfold loadedInverterInitialError loadedInverterError
    split
    · exact hadmissible.2.2.2.2.2.2.2.1
    · linarith [hadmissible.2.2.2.2.2.2.2.2.1]
  have hexp :
      Real.exp (-loadedInverterDecayRate world * time) ≤
        Real.exp (-loadedInverterDecayRate world * deadline) := by
    apply Real.exp_le_exp.mpr
    nlinarith [loadedInverterDecayRate_pos hadmissible]
  have hbound :
      loadedInverterErrorTrace world boundary time ≤ tolerance :=
    herror.trans <| (mul_le_mul_of_nonneg_left hexp hinitialNonnegative).trans
      hdeadline
  have hdomain :=
    loadedInverter_no_overshoot hadmissible hbehavior time htime
  cases hinput : world.environment.input with
  | false =>
      simp only [hinput, Bool.false_eq_true, if_false,
        loadedInverterErrorTrace, loadedInverterError] at hbound ⊢
      rw [abs_of_nonpos (by linarith)]
      simpa [sub_eq_add_neg, add_comm] using hbound
  | true =>
      simp only [hinput, if_true,
        loadedInverterErrorTrace, loadedInverterError] at hbound ⊢
      rw [sub_zero, abs_of_nonneg hdomain.1]
      exact hbound

end LeanModels.Spice

namespace LeanModels.Circuit

/-- Type-namespace wrapper so field notation on the shared parsed circuit
resolves without exposing the SPICE implementation namespace. -/
def ElaboratedCircuit.toLoadedInverterNominal
    (circuit : ElaboratedCircuit) :
    Except String LeanModels.Spice.LoadedInverterNominal :=
  LeanModels.Spice.ElaboratedCircuit.toLoadedInverterNominal circuit

end LeanModels.Circuit
