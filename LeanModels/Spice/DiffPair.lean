import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import LeanModels.Circuit
import LeanModels.Spice.Mos1
import LeanModels.Spice.CommonSource

/-!
# Matched NMOS differential pair with resistor loads and an ideal tail source

This is a FOCUSED slice in the `loaded_inverter`/`CommonSource` style, not
generic compilation: two matched NMOS transistors in the restricted MOS1
profile (`LEVEL=1`, `LAMBDA=0`, `IS=0`, positive `VTO`/`KP`) sharing a
source (tail) node, one matched drain resistor from each drain to a supply
port, and an IDEAL current source pulling `I_TAIL` from the tail node to
ground. Gate drivers and the supply belong to the run environment.

The DC behavior relation `DiffPairDC` contains ONLY physics: the two NMOS
channel-orientation admissibility conditions, KCL at each drain node (the
resistor Ohm law equated to the MOS1 channel law), and KCL at the tail
node (the two channel currents equated to the ideal source's current).
The balanced operating point, the differential transfer curve, the
differential gain, and the common-mode invariance are all THEOREMS derived
from that relation in the Specification layer below, never conjuncts of
it. Each drain equation is EXACTLY a common-source stage shifted by the
tail voltage (`diffPairDC_iff`), so the whole `CommonSource` solve library
is reused per side.

LOUD IDEALIZATION LABEL: with `LAMBDA = 0` the saturated channel current
does not depend on `V_DS`, and the ideal tail source holds its current at
ANY tail voltage (no compliance limit, arbitrarily far below ground). Under
exactly these two idealizations, common-mode rejection is an exact
invariance theorem (`diffPair_cmrr_ideal`): shifting the common mode moves
only the tail node, by exactly the shift, and moves the outputs not at
all — infinite CMRR. Real amplifiers only approximate this; channel-length
modulation and finite tail-source output resistance each break one premise.
The honest reading is that this theorem isolates WHAT ideal common-mode
rejection is, so that later refinements can quantify the deviation.

NOTE (future work feedstock): the differential-coordinate parametrization
(`cm ± d/2`), the matched-pair symmetry arguments, the tail-shift
invariance, and the balance-point analysis in this module are exactly the
ingredients the planned `DifferentialSenseBehavior` work needs for
sense-amplifier-style differential sensing. This module deliberately keeps
them in library form; it does not touch any DRAM module.
-/

namespace LeanModels.Spice

open LeanModels.Circuit
open Set

/-! ## Instance, environment, and behavior types -/

/-- Typed parameters fixed once for a fabricated differential pair: the
matched MOS1 device, the matched drain resistors, and the ideal tail
current. -/
structure DiffPairInstance where
  threshold : ℝ
  beta : ℝ
  drainResistance : ℝ
  tailCurrent : ℝ

/-- One DC run of one fabricated pair: the surrounding circuit holds the
supply and the two gate ports at fixed voltages. -/
structure DiffPairEnvironment where
  supply : ℝ
  inputP : ℝ
  inputN : ℝ

abbrev DiffPairWorld :=
  RunWorld DiffPairInstance DiffPairEnvironment Unit Unit

/-- Observable boundary behavior: the two drain (output) voltages. -/
structure DiffPairBoundary where
  outputP : ℝ
  outputN : ℝ

/-- Internal behavior: the shared source (tail) node voltage. -/
structure DiffPairInternal where
  tailVoltage : ℝ

/-- Each half of the pair, seen from its own drain, is a common-source
stage; this projection names that reuse. -/
def DiffPairInstance.side (fab : DiffPairInstance) : CommonSourceInstance :=
  { threshold := fab.threshold
    beta := fab.beta
    drainResistance := fab.drainResistance }

/-! ## Deck adapter -/

/-- Exact data recovered from a typed five-device differential-pair deck. -/
structure DiffPairNominal where
  inputPNode : LeanModels.Circuit.NodeId
  inputNNode : LeanModels.Circuit.NodeId
  outputPNode : LeanModels.Circuit.NodeId
  outputNNode : LeanModels.Circuit.NodeId
  supplyNode : LeanModels.Circuit.NodeId
  tailNode : LeanModels.Circuit.NodeId
  threshold : Rat
  beta : Rat
  drainResistance : Rat
  tailCurrent : Rat
deriving Repr, BEq, Inhabited

/-- Kernel-reducible pairwise-distinctness check for the port audit. -/
def diffPairNodesDistinct : List LeanModels.Circuit.NodeId → Bool
  | [] => true
  | node :: rest => rest.all (fun other => node != other) &&
      diffPairNodesDistinct rest

/-- Validate the complete matched-pair topology before exposing parameters
to the DC semantics: two NMOS devices on one `.model` card sharing a tail
node with grounded bulks, two equal drain resistors to one supply port
(either written terminal order accepted), and one ideal current source
from the tail node to ground. -/
def ElaboratedCircuit.toDiffPairNominal
    (circuit : ElaboratedCircuit) :
    Except String DiffPairNominal := do
  if circuit.devices.size != 5 then
    throw s!"differential pair requires exactly five devices, found {circuit.devices.size}"
  let mosfets := circuit.devices.toList.filterMap fun
    | .mosfet _ drain gate source bulk model =>
        some (drain, gate, source, bulk, model)
    | _ => none
  let resistors := circuit.devices.toList.filterMap fun
    | .resistor _ positive negative value =>
        some (positive, negative, value)
    | _ => none
  let currentSources := circuit.devices.toList.filterMap fun
    | .currentSource _ positive negative current =>
        some (positive, negative, current)
    | _ => none
  let ((drainP, gateP, sourceP, bulkP, modelP),
       (drainN, gateN, sourceN, bulkN, modelN)) ← match mosfets with
    | [mosfetP, mosfetN] => pure (mosfetP, mosfetN)
    | _ => throw "differential pair requires exactly two MOSFETs"
  unless modelP == modelN do
    throw "differential pair requires matched MOSFETs (one shared .model card)"
  let model ← match circuit.models[modelP.index]? with
    | some (.mos1 model) => pure model
    | _ => throw "MOSFET model is missing or unsupported"
  match model.polarity with
  | .pmos => throw "differential pair requires NMOS devices"
  | .nmos => pure ()
  unless model.channelLengthModulation == 0 &&
      model.junctionSaturation == 0 do
    throw "differential pair requires the named LAMBDA=0, IS=0 MOS1 profile"
  if model.threshold.num ≤ 0 || model.transconductance.num ≤ 0 then
    throw "differential pair requires positive VTO and KP"
  unless sourceP == sourceN do
    throw "differential pair requires one shared source (tail) node"
  let tailNode := sourceP
  unless bulkP == circuit.ground && bulkN == circuit.ground do
    throw "differential pair requires grounded bulks"
  let ((raPos, raNeg, raValue), (rbPos, rbNeg, rbValue)) ← match resistors with
    | [resistorA, resistorB] => pure (resistorA, resistorB)
    | _ => throw "differential pair requires exactly two drain resistors"
  let (supplyP, resistanceP, otherResistor) ←
    if raPos == drainP then pure (raNeg, raValue, (rbPos, rbNeg, rbValue))
    else if raNeg == drainP then pure (raPos, raValue, (rbPos, rbNeg, rbValue))
    else if rbPos == drainP then pure (rbNeg, rbValue, (raPos, raNeg, raValue))
    else if rbNeg == drainP then pure (rbPos, rbValue, (raPos, raNeg, raValue))
    else throw "a drain resistor must connect to the first MOSFET drain"
  let (roPos, roNeg, resistanceN) := otherResistor
  let supplyN ←
    if roPos == drainN then pure roNeg
    else if roNeg == drainN then pure roPos
    else throw "a drain resistor must connect to the second MOSFET drain"
  unless supplyP == supplyN do
    throw "the drain resistors must share one supply node"
  unless resistanceP == resistanceN do
    throw "differential pair requires matched drain resistors"
  if resistanceP.num ≤ 0 then
    throw "differential pair requires positive drain resistances"
  let (tailPos, tailNeg, tailCurrent) ← match currentSources with
    | [tailSource] => pure tailSource
    | _ => throw "differential pair requires exactly one tail current source"
  unless tailPos == tailNode && tailNeg == circuit.ground do
    throw "the tail source must pull current from the tail node to ground"
  if tailCurrent.num ≤ 0 then
    throw "differential pair requires a positive tail current"
  unless diffPairNodesDistinct
      [gateP, gateN, drainP, drainN, supplyP, tailNode, circuit.ground] do
    throw "differential-pair ports, tail, supply, and ground must be distinct"
  pure
    { inputPNode := gateP
      inputNNode := gateN
      outputPNode := drainP
      outputNNode := drainN
      supplyNode := supplyP
      tailNode
      threshold := model.threshold
      beta := model.transconductance
      drainResistance := resistanceP
      tailCurrent }

noncomputable def DiffPairNominal.instance
    (nominal : DiffPairNominal) : DiffPairInstance :=
  { threshold := nominal.threshold
    beta := nominal.beta
    drainResistance := nominal.drainResistance
    tailCurrent := nominal.tailCurrent }

noncomputable def DiffPairNominal.world
    (nominal : DiffPairNominal) (supply inputP inputN : ℝ) :
    DiffPairWorld :=
  deterministicWorld nominal.instance { supply, inputP, inputN }

/-! ## DC behavior relation (physics only)

Conjuncts: NMOS channel orientation for both devices (`Mos1DeviceLaw` with
the source at the tail node), KCL at each drain node (resistor Ohm law
equated to the MOS1 channel law), and KCL at the tail node (channel
currents summed into the ideal source's constitutive current). Nothing
else. -/

def DiffPairDC (fab : DiffPairInstance)
    (supply inputP inputN outputP outputN tail : ℝ) : Prop :=
  tail ≤ outputP ∧
  tail ≤ outputN ∧
  (supply - outputP) / fab.drainResistance =
    mos1ForwardCurrent
      { polarity := .nmos, threshold := fab.threshold,
        beta := fab.beta, lambda := 0 }
      (inputP - tail) (outputP - tail) ∧
  (supply - outputN) / fab.drainResistance =
    mos1ForwardCurrent
      { polarity := .nmos, threshold := fab.threshold,
        beta := fab.beta, lambda := 0 }
      (inputN - tail) (outputN - tail) ∧
  mos1ForwardCurrent
      { polarity := .nmos, threshold := fab.threshold,
        beta := fab.beta, lambda := 0 }
      (inputP - tail) (outputP - tail) +
    mos1ForwardCurrent
      { polarity := .nmos, threshold := fab.threshold,
        beta := fab.beta, lambda := 0 }
      (inputN - tail) (outputN - tail) =
    fab.tailCurrent

/-- The pair's DC denotation as a lane behavior relation. -/
def DiffPairBehavior :
    Behavior DiffPairWorld DiffPairBoundary DiffPairInternal :=
  fun world boundary internal =>
    DiffPairDC world.fabricated world.environment.supply
      world.environment.inputP world.environment.inputN
      boundary.outputP boundary.outputN internal.tailVoltage

/-- Physical and proof-domain conditions for a DC run. -/
def DiffPairAdmissible (world : DiffPairWorld) : Prop :=
  0 < world.fabricated.beta ∧
  0 < world.fabricated.threshold ∧
  0 < world.fabricated.drainResistance ∧
  0 < world.fabricated.tailCurrent ∧
  0 ≤ world.environment.supply

/-- Seen from either drain, the pair IS a common-source stage with supply,
gate, and drain all shifted by the tail voltage; the third conjunct is the
tail KCL restated through the two drain load lines. This is the reuse
theorem that lets every `CommonSource` solve apply per side. -/
theorem diffPairDC_iff {fab : DiffPairInstance}
    {supply inputP inputN outputP outputN tail : ℝ} :
    DiffPairDC fab supply inputP inputN outputP outputN tail ↔
      CommonSourceDC fab.side (supply - tail) (inputP - tail)
        (outputP - tail) ∧
      CommonSourceDC fab.side (supply - tail) (inputN - tail)
        (outputN - tail) ∧
      (supply - outputP) / fab.drainResistance +
        (supply - outputN) / fab.drainResistance = fab.tailCurrent := by
  unfold DiffPairDC CommonSourceDC
  dsimp only [DiffPairInstance.side]
  have hP : supply - tail - (outputP - tail) = supply - outputP := by ring
  have hN : supply - tail - (outputN - tail) = supply - outputN := by ring
  rw [hP, hN]
  constructor
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨by linarith, h3⟩, ⟨by linarith, h4⟩, by rw [h3, h4]; exact h5⟩
  · rintro ⟨⟨h1, h3⟩, ⟨h2, h4⟩, h5⟩
    exact ⟨by linarith, by linarith, h3, h4, by rw [← h3, ← h4]; exact h5⟩

/-! ## MOS1 gate-drive monotonicity

`CommonSource` proved the channel current monotone in the drain-source
drop; the pair's tail-node uniqueness additionally needs monotonicity (and
strictness on conducting channels) in the gate drive. Both are proved
branch-by-branch from the raw piecewise law. -/

/-- With `LAMBDA = 0` and a forward-oriented channel, the MOS1 current is
monotone nondecreasing in the gate drive. -/
theorem mos1ForwardCurrent_mono_gate
    (polarity : LeanModels.Circuit.MosPolarity) (threshold beta vds : ℝ)
    (hbeta : 0 ≤ beta) (hvds : 0 ≤ vds)
    {vgs₁ vgs₂ : ℝ} (hle : vgs₁ ≤ vgs₂) :
    mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 } vgs₁ vds ≤
      mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 } vgs₂ vds := by
  by_cases h1 : vgs₁ ≤ threshold
  · have hzero :
        mos1ForwardCurrent
          { polarity, threshold, beta, lambda := 0 } vgs₁ vds = 0 := by
      unfold mos1ForwardCurrent
      rw [if_pos h1]
    rw [hzero]
    exact mos1ForwardCurrent_nonneg polarity threshold beta vgs₂ vds
      hbeta hvds
  · have h2 : ¬ vgs₂ ≤ threshold := fun h => h1 (hle.trans h)
    unfold mos1ForwardCurrent
    rw [if_neg h1, if_neg h2]
    have hon1 : threshold < vgs₁ := lt_of_not_ge h1
    by_cases t1 : vds ≤ vgs₁ - threshold
    · have t2 : vds ≤ vgs₂ - threshold := by linarith
      rw [if_pos t1, if_pos t2]
      nlinarith [mul_nonneg hbeta (mul_nonneg hvds (sub_nonneg.mpr hle))]
    · rw [if_neg t1]
      by_cases t2 : vds ≤ vgs₂ - threshold
      · rw [if_pos t2]
        nlinarith [mul_nonneg hbeta
            (mul_nonneg
              (by linarith : (0 : ℝ) ≤ vds - (vgs₁ - threshold))
              (by linarith : (0 : ℝ) ≤ vds + (vgs₁ - threshold))),
          mul_nonneg hbeta
            (mul_nonneg
              (by linarith : (0 : ℝ) ≤ vgs₂ - threshold - vds) hvds)]
      · rw [if_neg t2]
        nlinarith [mul_nonneg hbeta
          (mul_nonneg (by linarith : (0 : ℝ) ≤ vgs₂ - vgs₁)
            (by linarith : (0 : ℝ) ≤ vgs₁ + vgs₂ - 2 * threshold))]

/-- On a conducting channel with a strictly positive drop, the gate-drive
monotonicity is strict. This is the strictness that pins the tail node. -/
theorem mos1ForwardCurrent_strict_mono_gate
    (polarity : LeanModels.Circuit.MosPolarity) (threshold beta vds : ℝ)
    (hbeta : 0 < beta) (hvds : 0 < vds)
    {vgs₁ vgs₂ : ℝ} (hon : threshold < vgs₁) (hlt : vgs₁ < vgs₂) :
    mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 } vgs₁ vds <
      mos1ForwardCurrent
        { polarity, threshold, beta, lambda := 0 } vgs₂ vds := by
  unfold mos1ForwardCurrent
  rw [if_neg (not_le.mpr hon), if_neg (not_le.mpr (hon.trans hlt))]
  by_cases t1 : vds ≤ vgs₁ - threshold
  · have t2 : vds ≤ vgs₂ - threshold := by linarith
    rw [if_pos t1, if_pos t2]
    nlinarith [mul_pos hbeta (mul_pos hvds (sub_pos.mpr hlt))]
  · rw [if_neg t1]
    by_cases t2 : vds ≤ vgs₂ - threshold
    · rw [if_pos t2]
      nlinarith [mul_pos hbeta
          (mul_pos (by linarith : (0 : ℝ) < vds - (vgs₁ - threshold))
            (by linarith : (0 : ℝ) < vds + (vgs₁ - threshold))),
        mul_nonneg hbeta.le
          (mul_nonneg
            (by linarith : (0 : ℝ) ≤ vgs₂ - threshold - vds) hvds.le)]
    · rw [if_neg t2]
      nlinarith [mul_pos hbeta
        (mul_pos (sub_pos.mpr hlt)
          (by linarith : (0 : ℝ) < vgs₁ + vgs₂ - 2 * threshold))]

/-- A strictly positive channel current certifies conduction. -/
theorem mos1ForwardCurrent_pos_gate
    {polarity : LeanModels.Circuit.MosPolarity}
    {threshold beta vgs vds : ℝ}
    (hpos : 0 < mos1ForwardCurrent
      { polarity, threshold, beta, lambda := 0 } vgs vds) :
    threshold < vgs := by
  by_contra hc
  push Not at hc
  unfold mos1ForwardCurrent at hpos
  rw [if_pos hc] at hpos
  exact lt_irrefl 0 hpos

/-- A strictly positive channel current certifies a strictly positive
drain-source drop. -/
theorem mos1ForwardCurrent_pos_drop
    {polarity : LeanModels.Circuit.MosPolarity}
    {threshold beta vgs vds : ℝ} (hvds : 0 ≤ vds)
    (hpos : 0 < mos1ForwardCurrent
      { polarity, threshold, beta, lambda := 0 } vgs vds) :
    0 < vds := by
  rcases hvds.lt_or_eq with h | h
  · exact h
  · exfalso
    rw [← h, mos1ForwardCurrent_zero_drop] at hpos
    exact lt_irrefl 0 hpos

/-! ## Determinacy

The tail node is pinned by a two-sided monotone argument: raising the tail
lowers both gate drives, and if a drain voltage also rose its load line
would demand a lower current — so both side currents are nonincreasing in
the tail voltage; the tail KCL then forces them equal, and on a conducting
side the strict gate monotonicity forbids two distinct tails. At equal
tails each side is a shifted common-source stage, whose determinacy
finishes the outputs. -/

theorem diffPair_dc_determinate
    {fab : DiffPairInstance} {supply inputP inputN : ℝ}
    {p₁ n₁ s₁ p₂ n₂ s₂ : ℝ}
    (hbeta : 0 < fab.beta) (hrd : 0 < fab.drainResistance)
    (htail : 0 < fab.tailCurrent)
    (h₁ : DiffPairDC fab supply inputP inputN p₁ n₁ s₁)
    (h₂ : DiffPairDC fab supply inputP inputN p₂ n₂ s₂) :
    p₁ = p₂ ∧ n₁ = n₂ ∧ s₁ = s₂ := by
  have key : ∀ pa na sa pb nb sb : ℝ,
      DiffPairDC fab supply inputP inputN pa na sa →
      DiffPairDC fab supply inputP inputN pb nb sb →
      sa < sb → False := by
    intro pa na sa pb nb sb ha hb hab
    obtain ⟨haP, haN, haPk, haNk, haT⟩ := ha
    obtain ⟨hbP, hbN, hbPk, hbNk, hbT⟩ := hb
    -- Each side's load-line current is nonincreasing in the tail voltage.
    have side : ∀ gate outa outb : ℝ,
        sa ≤ outa → sb ≤ outb →
        (supply - outa) / fab.drainResistance =
          mos1ForwardCurrent
            { polarity := .nmos, threshold := fab.threshold,
              beta := fab.beta, lambda := 0 }
            (gate - sa) (outa - sa) →
        (supply - outb) / fab.drainResistance =
          mos1ForwardCurrent
            { polarity := .nmos, threshold := fab.threshold,
              beta := fab.beta, lambda := 0 }
            (gate - sb) (outb - sb) →
        (supply - outb) / fab.drainResistance ≤
          (supply - outa) / fab.drainResistance := by
      intro gate outa outb hoa hob hka hkb
      rcases le_total outa outb with hoo | hoo
      · rw [div_le_div_iff₀ hrd hrd]
        nlinarith [mul_le_mul_of_nonneg_right
          (by linarith : supply - outb ≤ supply - outa) hrd.le]
      · rw [hka, hkb]
        calc mos1ForwardCurrent
              { polarity := .nmos, threshold := fab.threshold,
                beta := fab.beta, lambda := 0 }
              (gate - sb) (outb - sb)
            ≤ mos1ForwardCurrent
              { polarity := .nmos, threshold := fab.threshold,
                beta := fab.beta, lambda := 0 }
              (gate - sb) (outa - sa) :=
              mos1ForwardCurrent_mono_drop .nmos fab.threshold fab.beta _
                hbeta.le (by linarith)
          _ ≤ mos1ForwardCurrent
              { polarity := .nmos, threshold := fab.threshold,
                beta := fab.beta, lambda := 0 }
              (gate - sa) (outa - sa) :=
              mos1ForwardCurrent_mono_gate .nmos fab.threshold fab.beta _
                hbeta.le (by linarith) (by linarith)
    have hIbP := side inputP pa pb haP hbP haPk hbPk
    have hIbN := side inputN na nb haN hbN haNk hbNk
    have haSum : (supply - pa) / fab.drainResistance +
        (supply - na) / fab.drainResistance = fab.tailCurrent := by
      rw [haPk, haNk]; exact haT
    have hbSum : (supply - pb) / fab.drainResistance +
        (supply - nb) / fab.drainResistance = fab.tailCurrent := by
      rw [hbPk, hbNk]; exact hbT
    have hPeq : (supply - pb) / fab.drainResistance =
        (supply - pa) / fab.drainResistance := by linarith
    have hNeq : (supply - nb) / fab.drainResistance =
        (supply - na) / fab.drainResistance := by linarith
    have hpeq : pb = pa := by
      rw [div_eq_div_iff hrd.ne' hrd.ne'] at hPeq
      have := mul_right_cancel₀ hrd.ne' hPeq
      linarith
    have hneq : nb = na := by
      rw [div_eq_div_iff hrd.ne' hrd.ne'] at hNeq
      have := mul_right_cancel₀ hrd.ne' hNeq
      linarith
    rw [hpeq] at hbPk hbP
    rw [hneq] at hbNk hbN
    -- A conducting side exists at the higher tail (the tail current is
    -- positive), and strict gate monotonicity contradicts equal currents
    -- at two distinct tails there.
    have conduct : ∀ gate out : ℝ,
        sa ≤ out → sb ≤ out →
        (supply - out) / fab.drainResistance =
          mos1ForwardCurrent
            { polarity := .nmos, threshold := fab.threshold,
              beta := fab.beta, lambda := 0 }
            (gate - sa) (out - sa) →
        (supply - out) / fab.drainResistance =
          mos1ForwardCurrent
            { polarity := .nmos, threshold := fab.threshold,
              beta := fab.beta, lambda := 0 }
            (gate - sb) (out - sb) →
        0 < mos1ForwardCurrent
          { polarity := .nmos, threshold := fab.threshold,
            beta := fab.beta, lambda := 0 }
          (gate - sb) (out - sb) → False := by
      intro gate out hoa hob hka hkb hpos
      have heq : mos1ForwardCurrent
          { polarity := .nmos, threshold := fab.threshold,
            beta := fab.beta, lambda := 0 }
          (gate - sb) (out - sb) =
        mos1ForwardCurrent
          { polarity := .nmos, threshold := fab.threshold,
            beta := fab.beta, lambda := 0 }
          (gate - sa) (out - sa) := by
        rw [← hka, ← hkb]
      have hon : fab.threshold < gate - sb :=
        mos1ForwardCurrent_pos_gate hpos
      have hvds : 0 < out - sb :=
        mos1ForwardCurrent_pos_drop (by linarith) hpos
      have hstrict :=
        mos1ForwardCurrent_strict_mono_gate .nmos fab.threshold fab.beta
          (out - sb) hbeta hvds hon (by linarith : gate - sb < gate - sa)
      have hmono :=
        mos1ForwardCurrent_mono_drop .nmos fab.threshold fab.beta
          (gate - sa) hbeta.le (by linarith : out - sb ≤ out - sa)
      linarith [heq, hstrict, hmono]
    have hnnP : 0 ≤ mos1ForwardCurrent
        { polarity := .nmos, threshold := fab.threshold,
          beta := fab.beta, lambda := 0 }
        (inputP - sb) (pa - sb) :=
      mos1ForwardCurrent_nonneg .nmos fab.threshold fab.beta _ _
        hbeta.le (by linarith)
    have hnnN : 0 ≤ mos1ForwardCurrent
        { polarity := .nmos, threshold := fab.threshold,
          beta := fab.beta, lambda := 0 }
        (inputN - sb) (na - sb) :=
      mos1ForwardCurrent_nonneg .nmos fab.threshold fab.beta _ _
        hbeta.le (by linarith)
    have hsplit : 0 < mos1ForwardCurrent
          { polarity := .nmos, threshold := fab.threshold,
            beta := fab.beta, lambda := 0 }
          (inputP - sb) (pa - sb) ∨
        0 < mos1ForwardCurrent
          { polarity := .nmos, threshold := fab.threshold,
            beta := fab.beta, lambda := 0 }
          (inputN - sb) (na - sb) := by
      by_contra hcon
      push Not at hcon
      obtain ⟨hc1, hc2⟩ := hcon
      linarith [hbT]
    rcases hsplit with hpos | hpos
    · exact conduct inputP pa haP hbP haPk hbPk hpos
    · exact conduct inputN na haN hbN haNk hbNk hpos
  have hs : s₁ = s₂ := by
    rcases lt_trichotomy s₁ s₂ with h | h | h
    · exact (key p₁ n₁ s₁ p₂ n₂ s₂ h₁ h₂ h).elim
    · exact h
    · exact (key p₂ n₂ s₂ p₁ n₁ s₁ h₂ h₁ h).elim
  subst hs
  obtain ⟨hcs1P, hcs1N, -⟩ := diffPairDC_iff.mp h₁
  obtain ⟨hcs2P, hcs2N, -⟩ := diffPairDC_iff.mp h₂
  have hP := commonSource_dc_determinate (fabricated := fab.side)
    hbeta.le hrd hcs1P hcs2P
  have hN := commonSource_dc_determinate (fabricated := fab.side)
    hbeta.le hrd hcs1N hcs2N
  exact ⟨by linarith, by linarith, rfl⟩

/-! ## Specification layer: derived quantities

Names for the closed forms the physics relation forces. None of these
appear in `DiffPairDC`; every connection below is re-derived through the
behavior relation. -/

/-- The derived common overdrive at differential drive `d`:
`√(I_T/β − d²/4)`. At balance it is `√(I_T/β)`. -/
noncomputable def diffPairOverdrive (fab : DiffPairInstance) (d : ℝ) : ℝ :=
  Real.sqrt (fab.tailCurrent / fab.beta - d ^ 2 / 4)

/-- The derived tail-node voltage: the source node tracks the common mode
at the fixed offset `V_TO + overdrive`. -/
noncomputable def diffPairTail (fab : DiffPairInstance) (cm d : ℝ) : ℝ :=
  cm - fab.threshold - diffPairOverdrive fab d

/-- The derived positive-side output. -/
noncomputable def diffPairOutP (fab : DiffPairInstance) (supply d : ℝ) : ℝ :=
  supply - fab.drainResistance *
    (fab.beta / 2 * (diffPairOverdrive fab d + d / 2) ^ 2)

/-- The derived negative-side output. -/
noncomputable def diffPairOutN (fab : DiffPairInstance) (supply d : ℝ) : ℝ :=
  supply - fab.drainResistance *
    (fab.beta / 2 * (diffPairOverdrive fab d - d / 2) ^ 2)

/-- Conduction window on the environment: the differential drive is small
enough that neither side cuts off (beyond `d² = 2·I_T/β` the pair fully
switches). -/
def DiffPairConducting (fab : DiffPairInstance) (d : ℝ) : Prop :=
  d ^ 2 < 2 * (fab.tailCurrent / fab.beta)

/-- Saturation window on the environment: the common mode is low enough
that both drains stay at or above their overdrive throughout the drive
`d`. At `d = 0` this is exactly `cm + R_D·I_T/2 ≤ V_DD + V_TO`. -/
def DiffPairSaturationWindow (fab : DiffPairInstance)
    (supply cm d : ℝ) : Prop :=
  cm + |d| / 2 + fab.drainResistance * fab.beta / 2 *
      (Real.sqrt (fab.tailCurrent / fab.beta) + |d| / 2) ^ 2 ≤
    supply + fab.threshold

/-! ## Realizability: the derived state IS a DC state

The construction goes through `diffPairDC_iff`: each side is the derived
transfer point of its tail-shifted common-source stage, and the tail KCL
closes because the two saturation currents sum to `β·(u² + d²/4) = I_T`
by the very definition of the derived overdrive. -/

theorem diffPair_dc_transfer_realizable
    {fab : DiffPairInstance} {supply cm d : ℝ}
    (hbeta : 0 < fab.beta) (hrd : 0 < fab.drainResistance)
    (htail : 0 < fab.tailCurrent)
    (hcond : DiffPairConducting fab d)
    (hwin : DiffPairSaturationWindow fab supply cm d) :
    DiffPairDC fab supply (cm + d / 2) (cm - d / 2)
      (diffPairOutP fab supply d) (diffPairOutN fab supply d)
      (diffPairTail fab cm d) := by
  unfold DiffPairConducting at hcond
  unfold DiffPairSaturationWindow at hwin
  have hc : 0 < fab.tailCurrent / fab.beta := div_pos htail hbeta
  have hcs : 0 ≤ Real.sqrt (fab.tailCurrent / fab.beta) :=
    Real.sqrt_nonneg _
  have harg : 0 ≤ fab.tailCurrent / fab.beta - d ^ 2 / 4 := by nlinarith
  rw [diffPairDC_iff]
  unfold diffPairOutP diffPairOutN diffPairTail diffPairOverdrive
  set u := Real.sqrt (fab.tailCurrent / fab.beta - d ^ 2 / 4) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu2 : u ^ 2 = fab.tailCurrent / fab.beta - d ^ 2 / 4 :=
    Real.sq_sqrt harg
  have husq : u ≤ Real.sqrt (fab.tailCurrent / fab.beta) :=
    Real.sqrt_le_sqrt (by linarith [sq_nonneg d])
  have habs2 : (|d| / 2) ^ 2 = d ^ 2 / 4 := by
    rw [div_pow, sq_abs]; norm_num
  have hud : |d| / 2 < u := by
    have h1 : (|d| / 2) ^ 2 < u ^ 2 := by rw [habs2, hu2]; nlinarith
    exact lt_of_pow_lt_pow_left₀ 2 hu0 h1
  have hdplus : 0 < u + d / 2 := by
    have := neg_abs_le d
    linarith
  have hdminus : 0 < u - d / 2 := by
    have := le_abs_self d
    linarith
  have hbrdn : (0 : ℝ) ≤ fab.beta * fab.drainResistance / 2 :=
    div_nonneg (mul_pos hbeta hrd).le (by norm_num)
  have hsqP : (u + d / 2) ^ 2 ≤
      (Real.sqrt (fab.tailCurrent / fab.beta) + |d| / 2) ^ 2 := by
    nlinarith [mul_nonneg
      (by linarith [le_abs_self d] : (0 : ℝ) ≤
        Real.sqrt (fab.tailCurrent / fab.beta) + |d| / 2 - (u + d / 2))
      (by linarith [neg_abs_le d] : (0 : ℝ) ≤
        Real.sqrt (fab.tailCurrent / fab.beta) + |d| / 2 + (u + d / 2))]
  have hsqN : (u - d / 2) ^ 2 ≤
      (Real.sqrt (fab.tailCurrent / fab.beta) + |d| / 2) ^ 2 := by
    nlinarith [mul_nonneg
      (by linarith [neg_abs_le d] : (0 : ℝ) ≤
        Real.sqrt (fab.tailCurrent / fab.beta) + |d| / 2 - (u - d / 2))
      (by linarith [le_abs_self d] : (0 : ℝ) ≤
        Real.sqrt (fab.tailCurrent / fab.beta) + |d| / 2 + (u - d / 2))]
  have hscaleP := mul_le_mul_of_nonneg_left hsqP hbrdn
  have hscaleN := mul_le_mul_of_nonneg_left hsqN hbrdn
  refine ⟨?_, ?_, ?_⟩
  · have honP : fab.side.threshold <
        cm + d / 2 - (cm - fab.threshold - u) := by
      dsimp only [DiffPairInstance.side]
      linarith
    have hwinP : fab.side.beta * fab.side.drainResistance / 2 *
        (cm + d / 2 - (cm - fab.threshold - u) - fab.side.threshold) ^ 2 +
        (cm + d / 2 - (cm - fab.threshold - u) - fab.side.threshold) ≤
        supply - (cm - fab.threshold - u) := by
      dsimp only [DiffPairInstance.side]
      have hXP : cm + d / 2 - (cm - fab.threshold - u) - fab.threshold =
          u + d / 2 := by ring
      rw [hXP]
      nlinarith [hscaleP, hwin, le_abs_self d]
    have h := commonSource_dc_transfer_realizable (fabricated := fab.side)
      (supply := supply - (cm - fab.threshold - u))
      (input := cm + d / 2 - (cm - fab.threshold - u))
      hbeta hrd honP hwinP
    have hout : commonSourceTransfer fab.side
        (supply - (cm - fab.threshold - u))
        (cm + d / 2 - (cm - fab.threshold - u)) =
        supply - fab.drainResistance * (fab.beta / 2 * (u + d / 2) ^ 2) -
          (cm - fab.threshold - u) := by
      unfold commonSourceTransfer
      dsimp only [DiffPairInstance.side]
      ring
    rw [hout] at h
    exact h
  · have honN : fab.side.threshold <
        cm - d / 2 - (cm - fab.threshold - u) := by
      dsimp only [DiffPairInstance.side]
      linarith
    have hwinN : fab.side.beta * fab.side.drainResistance / 2 *
        (cm - d / 2 - (cm - fab.threshold - u) - fab.side.threshold) ^ 2 +
        (cm - d / 2 - (cm - fab.threshold - u) - fab.side.threshold) ≤
        supply - (cm - fab.threshold - u) := by
      dsimp only [DiffPairInstance.side]
      have hXN : cm - d / 2 - (cm - fab.threshold - u) - fab.threshold =
          u - d / 2 := by ring
      rw [hXN]
      nlinarith [hscaleN, hwin, neg_abs_le d]
    have h := commonSource_dc_transfer_realizable (fabricated := fab.side)
      (supply := supply - (cm - fab.threshold - u))
      (input := cm - d / 2 - (cm - fab.threshold - u))
      hbeta hrd honN hwinN
    have hout : commonSourceTransfer fab.side
        (supply - (cm - fab.threshold - u))
        (cm - d / 2 - (cm - fab.threshold - u)) =
        supply - fab.drainResistance * (fab.beta / 2 * (u - d / 2) ^ 2) -
          (cm - fab.threshold - u) := by
      unfold commonSourceTransfer
      dsimp only [DiffPairInstance.side]
      ring
    rw [hout] at h
    exact h
  · have hP3 : supply - (supply - fab.drainResistance *
        (fab.beta / 2 * (u + d / 2) ^ 2)) =
        fab.drainResistance * (fab.beta / 2 * (u + d / 2) ^ 2) := by ring
    have hN3 : supply - (supply - fab.drainResistance *
        (fab.beta / 2 * (u - d / 2) ^ 2)) =
        fab.drainResistance * (fab.beta / 2 * (u - d / 2) ^ 2) := by ring
    rw [hP3, hN3, mul_div_cancel_left₀ _ hrd.ne',
      mul_div_cancel_left₀ _ hrd.ne']
    have hexp : fab.beta / 2 * (u + d / 2) ^ 2 +
        fab.beta / 2 * (u - d / 2) ^ 2 =
        fab.beta * (u ^ 2 + d ^ 2 / 4) := by ring
    rw [hexp, hu2]
    have hcancel : fab.tailCurrent / fab.beta - d ^ 2 / 4 + d ^ 2 / 4 =
        fab.tailCurrent / fab.beta := by ring
    rw [hcancel, mul_comm]
    exact div_mul_cancel₀ _ hbeta.ne'

/-! ## The derived operating point, for every DC state in the window -/

/-- Inside the conduction and saturation windows, EVERY DC state sits at
the derived transfer point: outputs and tail node are pinned by
determinacy against the constructed state. Everything on the right-hand
side is Specification-layer; nothing is asserted in the behavior
relation. -/
theorem diffPair_dc_op
    {fab : DiffPairInstance} {supply cm d outputP outputN tail : ℝ}
    (hbeta : 0 < fab.beta) (hrd : 0 < fab.drainResistance)
    (htail : 0 < fab.tailCurrent)
    (hcond : DiffPairConducting fab d)
    (hwin : DiffPairSaturationWindow fab supply cm d)
    (hdc : DiffPairDC fab supply (cm + d / 2) (cm - d / 2)
      outputP outputN tail) :
    outputP = diffPairOutP fab supply d ∧
    outputN = diffPairOutN fab supply d ∧
    tail = diffPairTail fab cm d :=
  diffPair_dc_determinate hbeta hrd htail hdc
    (diffPair_dc_transfer_realizable hbeta hrd htail hcond hwin)

/-- The exact large-signal differential output: every DC state in the
window satisfies `v_outP − v_outN = −R_D·β·d·√(I_T/β − d²/4)` — the
textbook differential transfer characteristic, derived. -/
theorem diffPair_dc_diff_output
    {fab : DiffPairInstance} {supply cm d outputP outputN tail : ℝ}
    (hbeta : 0 < fab.beta) (hrd : 0 < fab.drainResistance)
    (htail : 0 < fab.tailCurrent)
    (hcond : DiffPairConducting fab d)
    (hwin : DiffPairSaturationWindow fab supply cm d)
    (hdc : DiffPairDC fab supply (cm + d / 2) (cm - d / 2)
      outputP outputN tail) :
    outputP - outputN =
      -(fab.drainResistance * fab.beta * d *
        Real.sqrt (fab.tailCurrent / fab.beta - d ^ 2 / 4)) := by
  obtain ⟨hP, hN, -⟩ := diffPair_dc_op hbeta hrd htail hcond hwin hdc
  rw [hP, hN]
  unfold diffPairOutP diffPairOutN diffPairOverdrive
  ring

/-! ## Balanced operating point and common-mode window -/

private theorem diffPair_conducting_zero
    {fab : DiffPairInstance}
    (hbeta : 0 < fab.beta) (htail : 0 < fab.tailCurrent) :
    DiffPairConducting fab 0 := by
  unfold DiffPairConducting
  nlinarith [div_pos htail hbeta]

private theorem diffPair_balanced_window
    {fab : DiffPairInstance} {supply cm : ℝ}
    (hbeta : 0 < fab.beta) (htail : 0 < fab.tailCurrent)
    (hwin : cm + fab.drainResistance * fab.tailCurrent / 2 ≤
      supply + fab.threshold) :
    DiffPairSaturationWindow fab supply cm 0 := by
  unfold DiffPairSaturationWindow
  have hc : 0 < fab.tailCurrent / fab.beta := div_pos htail hbeta
  have hz : Real.sqrt (fab.tailCurrent / fab.beta) + 0 / 2 =
      Real.sqrt (fab.tailCurrent / fab.beta) := by norm_num
  rw [abs_zero, hz, Real.sq_sqrt hc.le]
  have hβ : fab.beta * (fab.tailCurrent / fab.beta) = fab.tailCurrent := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hbeta.ne'
  have hRIT : fab.drainResistance * fab.beta / 2 *
      (fab.tailCurrent / fab.beta) =
      fab.drainResistance * fab.tailCurrent / 2 := by
    calc fab.drainResistance * fab.beta / 2 *
        (fab.tailCurrent / fab.beta)
        = fab.drainResistance *
            (fab.beta * (fab.tailCurrent / fab.beta)) / 2 := by ring
      _ = fab.drainResistance * fab.tailCurrent / 2 := by rw [hβ]
  linarith [hRIT, hwin]

private theorem diffPair_outP_zero
    {fab : DiffPairInstance} (supply : ℝ)
    (hbeta : 0 < fab.beta) (htail : 0 < fab.tailCurrent) :
    diffPairOutP fab supply 0 =
      supply - fab.drainResistance * fab.tailCurrent / 2 := by
  unfold diffPairOutP diffPairOverdrive
  have hc : 0 < fab.tailCurrent / fab.beta := div_pos htail hbeta
  have hz : fab.tailCurrent / fab.beta - (0 : ℝ) ^ 2 / 4 =
      fab.tailCurrent / fab.beta := by norm_num
  rw [hz]
  have hz2 : Real.sqrt (fab.tailCurrent / fab.beta) + 0 / 2 =
      Real.sqrt (fab.tailCurrent / fab.beta) := by norm_num
  rw [hz2, Real.sq_sqrt hc.le]
  have hβ : fab.beta * (fab.tailCurrent / fab.beta) = fab.tailCurrent := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hbeta.ne'
  calc supply - fab.drainResistance *
      (fab.beta / 2 * (fab.tailCurrent / fab.beta))
      = supply - fab.drainResistance *
          (fab.beta * (fab.tailCurrent / fab.beta)) / 2 := by ring
    _ = supply - fab.drainResistance * fab.tailCurrent / 2 := by rw [hβ]

private theorem diffPair_outN_zero
    {fab : DiffPairInstance} (supply : ℝ)
    (hbeta : 0 < fab.beta) (htail : 0 < fab.tailCurrent) :
    diffPairOutN fab supply 0 =
      supply - fab.drainResistance * fab.tailCurrent / 2 := by
  unfold diffPairOutN diffPairOverdrive
  have hc : 0 < fab.tailCurrent / fab.beta := div_pos htail hbeta
  have hz : fab.tailCurrent / fab.beta - (0 : ℝ) ^ 2 / 4 =
      fab.tailCurrent / fab.beta := by norm_num
  rw [hz]
  have hz2 : Real.sqrt (fab.tailCurrent / fab.beta) - 0 / 2 =
      Real.sqrt (fab.tailCurrent / fab.beta) := by norm_num
  rw [hz2, Real.sq_sqrt hc.le]
  have hβ : fab.beta * (fab.tailCurrent / fab.beta) = fab.tailCurrent := by
    rw [mul_comm]
    exact div_mul_cancel₀ _ hbeta.ne'
  calc supply - fab.drainResistance *
      (fab.beta / 2 * (fab.tailCurrent / fab.beta))
      = supply - fab.drainResistance *
          (fab.beta * (fab.tailCurrent / fab.beta)) / 2 := by ring
    _ = supply - fab.drainResistance * fab.tailCurrent / 2 := by rw [hβ]

private theorem diffPair_tail_zero
    {fab : DiffPairInstance} (cm : ℝ) :
    diffPairTail fab cm 0 =
      cm - fab.threshold - Real.sqrt (fab.tailCurrent / fab.beta) := by
  unfold diffPairTail diffPairOverdrive
  norm_num

/-- THE BALANCED OPERATING POINT, derived. At zero differential drive,
inside the balanced common-mode window `cm + R_D·I_T/2 ≤ V_DD + V_TO`,
every DC state has both outputs at exactly `V_DD − R_D·I_T/2` and the
tail node tracking the common mode at exactly `cm − V_TO − √(I_T/β)`. -/
theorem diffPair_dc_balanced
    {fab : DiffPairInstance} {supply cm outputP outputN tail : ℝ}
    (hbeta : 0 < fab.beta) (hrd : 0 < fab.drainResistance)
    (htail : 0 < fab.tailCurrent)
    (hwin : cm + fab.drainResistance * fab.tailCurrent / 2 ≤
      supply + fab.threshold)
    (hdc : DiffPairDC fab supply cm cm outputP outputN tail) :
    outputP = supply - fab.drainResistance * fab.tailCurrent / 2 ∧
    outputN = supply - fab.drainResistance * fab.tailCurrent / 2 ∧
    tail = cm - fab.threshold -
      Real.sqrt (fab.tailCurrent / fab.beta) := by
  have hdc0 : DiffPairDC fab supply (cm + 0 / 2) (cm - 0 / 2)
      outputP outputN tail := by
    norm_num
    exact hdc
  obtain ⟨hP, hN, hT⟩ := diffPair_dc_op hbeta hrd htail
    (diffPair_conducting_zero hbeta htail)
    (diffPair_balanced_window hbeta htail hwin) hdc0
  exact ⟨by rw [hP, diffPair_outP_zero supply hbeta htail],
    by rw [hN, diffPair_outN_zero supply hbeta htail],
    by rw [hT, diffPair_tail_zero]⟩

/-- Realizability twin for the balanced operating point: the derived
balanced state IS a DC state, for every common mode in the window. -/
theorem diffPair_dc_balanced_realizable
    {fab : DiffPairInstance} {supply cm : ℝ}
    (hbeta : 0 < fab.beta) (hrd : 0 < fab.drainResistance)
    (htail : 0 < fab.tailCurrent)
    (hwin : cm + fab.drainResistance * fab.tailCurrent / 2 ≤
      supply + fab.threshold) :
    DiffPairDC fab supply cm cm
      (supply - fab.drainResistance * fab.tailCurrent / 2)
      (supply - fab.drainResistance * fab.tailCurrent / 2)
      (cm - fab.threshold - Real.sqrt (fab.tailCurrent / fab.beta)) := by
  have h := diffPair_dc_transfer_realizable hbeta hrd htail
    (diffPair_conducting_zero hbeta htail)
    (diffPair_balanced_window hbeta htail hwin)
  rw [diffPair_outP_zero supply hbeta htail,
    diffPair_outN_zero supply hbeta htail, diffPair_tail_zero] at h
  norm_num at h
  exact h

/-! ## Ideal-tail common-mode rejection -/

/-- IDEAL-TAIL COMMON-MODE REJECTION — an EXACT invariance theorem, and a
loudly-labeled idealization. With `LAMBDA = 0` (saturated channel current
independent of `V_DS`) and the IDEAL tail source (exact `I_T` at any tail
voltage), shifting the common mode from `cm` to `cm'` anywhere inside the
saturation window moves the tail node by exactly `cm' − cm` and moves
neither output at all: infinite CMRR. Real amplifiers only approximate
this; channel-length modulation and finite tail-source output resistance
each break one premise. This theorem states exactly WHAT ideal common-mode
rejection is, so later refinements can quantify the deviation from it. -/
theorem diffPair_cmrr_ideal
    {fab : DiffPairInstance} {supply cm cm' d : ℝ}
    {outputP outputN tail outputP' outputN' tail' : ℝ}
    (hbeta : 0 < fab.beta) (hrd : 0 < fab.drainResistance)
    (htail : 0 < fab.tailCurrent)
    (hcond : DiffPairConducting fab d)
    (hwin : DiffPairSaturationWindow fab supply cm d)
    (hwin' : DiffPairSaturationWindow fab supply cm' d)
    (hdc : DiffPairDC fab supply (cm + d / 2) (cm - d / 2)
      outputP outputN tail)
    (hdc' : DiffPairDC fab supply (cm' + d / 2) (cm' - d / 2)
      outputP' outputN' tail') :
    outputP' = outputP ∧ outputN' = outputN ∧
    tail' - tail = cm' - cm := by
  obtain ⟨e1, e2, e3⟩ := diffPair_dc_op hbeta hrd htail hcond hwin hdc
  obtain ⟨f1, f2, f3⟩ := diffPair_dc_op hbeta hrd htail hcond hwin' hdc'
  refine ⟨by rw [e1, f1], by rw [e2, f2], ?_⟩
  rw [e3, f3]
  unfold diffPairTail
  ring

/-- Realizability twin for the common-mode invariance: at both common
modes the DC states exist, and they exhibit the exact invariance. -/
theorem diffPair_cmrr_realizable
    {fab : DiffPairInstance} {supply cm cm' d : ℝ}
    (hbeta : 0 < fab.beta) (hrd : 0 < fab.drainResistance)
    (htail : 0 < fab.tailCurrent)
    (hcond : DiffPairConducting fab d)
    (hwin : DiffPairSaturationWindow fab supply cm d)
    (hwin' : DiffPairSaturationWindow fab supply cm' d) :
    ∃ outputP outputN tail outputP' outputN' tail',
      DiffPairDC fab supply (cm + d / 2) (cm - d / 2)
        outputP outputN tail ∧
      DiffPairDC fab supply (cm' + d / 2) (cm' - d / 2)
        outputP' outputN' tail' ∧
      outputP' = outputP ∧ outputN' = outputN ∧
      tail' - tail = cm' - cm := by
  refine ⟨_, _, _, _, _, _,
    diffPair_dc_transfer_realizable hbeta hrd htail hcond hwin,
    diffPair_dc_transfer_realizable hbeta hrd htail hcond hwin',
    rfl, rfl, ?_⟩
  unfold diffPairTail
  ring

/-! ## Differential gain as a literal derivative -/

/-- The derived differential output
`d ↦ v_outP − v_outN = −R_D·β·d·√(I_T/β − d²/4)` has the textbook
derivative `−g_m·R_D = −R_D·β·√(I_T/β)` at balance. -/
theorem diffPair_transfer_hasDerivAt
    (fab : DiffPairInstance) (supply : ℝ)
    (hbeta : 0 < fab.beta) (htail : 0 < fab.tailCurrent) :
    HasDerivAt
      (fun d => diffPairOutP fab supply d - diffPairOutN fab supply d)
      (-(fab.drainResistance * fab.beta *
        Real.sqrt (fab.tailCurrent / fab.beta))) 0 := by
  have hc : 0 < fab.tailCurrent / fab.beta := div_pos htail hbeta
  have hinner : HasDerivAt
      (fun d : ℝ => fab.tailCurrent / fab.beta - d ^ 2 / 4) (0 : ℝ) 0 := by
    have hpow : HasDerivAt (fun d : ℝ => d ^ 2) (0 : ℝ) 0 := by
      simpa using hasDerivAt_pow 2 (0 : ℝ)
    simpa using (hpow.div_const 4).const_sub (fab.tailCurrent / fab.beta)
  have hsqrt : HasDerivAt
      (fun d : ℝ => Real.sqrt (fab.tailCurrent / fab.beta - d ^ 2 / 4))
      (0 : ℝ) 0 := by
    have h := hinner.sqrt (by norm_num [hc.ne'])
    simpa using h
  have hlin : HasDerivAt
      (fun d : ℝ => -(fab.drainResistance * fab.beta) * d)
      (-(fab.drainResistance * fab.beta)) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul
      (-(fab.drainResistance * fab.beta))
  have hprod := hlin.mul hsqrt
  have htarget := hprod.congr_deriv
    (show -(fab.drainResistance * fab.beta) *
          Real.sqrt (fab.tailCurrent / fab.beta - (0 : ℝ) ^ 2 / 4) +
        -(fab.drainResistance * fab.beta) * 0 * 0 =
      -(fab.drainResistance * fab.beta *
        Real.sqrt (fab.tailCurrent / fab.beta)) by norm_num)
  apply htarget.congr_of_eventuallyEq
  filter_upwards with d
  simp only [Pi.mul_apply]
  unfold diffPairOutP diffPairOutN diffPairOverdrive
  ring

private theorem diffPair_conducting_of_lt
    {fab : DiffPairInstance} {m d : ℝ} (habs : |d| < m)
    (hcond : m ^ 2 ≤ 2 * (fab.tailCurrent / fab.beta)) :
    DiffPairConducting fab d := by
  unfold DiffPairConducting
  obtain ⟨h1, h2⟩ := abs_lt.mp habs
  have := sq_lt_sq' h1 h2
  linarith

private theorem diffPair_window_of_lt
    {fab : DiffPairInstance} {supply cm m d : ℝ}
    (hbeta : 0 < fab.beta) (hrd : 0 < fab.drainResistance)
    (habs : |d| < m)
    (hwin : cm + m / 2 + fab.drainResistance * fab.beta / 2 *
        (Real.sqrt (fab.tailCurrent / fab.beta) + m / 2) ^ 2 ≤
      supply + fab.threshold) :
    DiffPairSaturationWindow fab supply cm d := by
  unfold DiffPairSaturationWindow
  have hsq : (Real.sqrt (fab.tailCurrent / fab.beta) + |d| / 2) ^ 2 ≤
      (Real.sqrt (fab.tailCurrent / fab.beta) + m / 2) ^ 2 := by
    nlinarith [mul_nonneg
      (by linarith : (0 : ℝ) ≤ m / 2 - |d| / 2)
      (by linarith [Real.sqrt_nonneg (fab.tailCurrent / fab.beta),
          abs_nonneg d] : (0 : ℝ) ≤
        2 * Real.sqrt (fab.tailCurrent / fab.beta) + m / 2 + |d| / 2)]
  have hscale := mul_le_mul_of_nonneg_left hsq
    (div_nonneg (mul_pos hrd hbeta).le (by norm_num : (0 : ℝ) ≤ 2))
  linarith [hwin, habs, hscale]

/-- THE DIFFERENTIAL GAIN THEOREM. Any solution family of the physics-only
DC relation in differential coordinates (`inputs cm ± d/2`) on a
symmetric window around balance has a literal mathlib derivative of its
differential output at `d = 0`, and it equals `−g_m·R_D =
−R_D·β·√(I_T/β)`: the behavior relation pins every solution family to the
derived differential transfer curve on a neighborhood of balance, so
differentiability and the gain value transfer over. -/
theorem diffPair_gain
    {fab : DiffPairInstance} {supply cm m : ℝ}
    (hbeta : 0 < fab.beta) (hrd : 0 < fab.drainResistance)
    (htail : 0 < fab.tailCurrent) (hm : 0 < m)
    (hcond : m ^ 2 ≤ 2 * (fab.tailCurrent / fab.beta))
    (hwin : cm + m / 2 + fab.drainResistance * fab.beta / 2 *
        (Real.sqrt (fab.tailCurrent / fab.beta) + m / 2) ^ 2 ≤
      supply + fab.threshold)
    {vop von vtail : ℝ → ℝ}
    (hsol : ∀ d ∈ Set.Ioo (-m) m,
      DiffPairDC fab supply (cm + d / 2) (cm - d / 2)
        (vop d) (von d) (vtail d)) :
    HasDerivAt (fun d => vop d - von d)
      (-(fab.drainResistance * fab.beta *
        Real.sqrt (fab.tailCurrent / fab.beta))) 0 := by
  apply (diffPair_transfer_hasDerivAt fab supply hbeta
    htail).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr hm) hm] with d hd
  have habs : |d| < m := abs_lt.mpr ⟨hd.1, hd.2⟩
  obtain ⟨e1, e2, -⟩ := diffPair_dc_op hbeta hrd htail
    (diffPair_conducting_of_lt habs hcond)
    (diffPair_window_of_lt hbeta hrd habs hwin) (hsol d hd)
  rw [e1, e2]

/-- Realizability twin for the differential gain theorem: a solution
family satisfying its hypothesis exists — the derived transfer curves
themselves — with the same literal derivative at balance. -/
theorem diffPair_gain_realizable
    {fab : DiffPairInstance} {supply cm m : ℝ}
    (hbeta : 0 < fab.beta) (hrd : 0 < fab.drainResistance)
    (htail : 0 < fab.tailCurrent) (_hm : 0 < m)
    (hcond : m ^ 2 ≤ 2 * (fab.tailCurrent / fab.beta))
    (hwin : cm + m / 2 + fab.drainResistance * fab.beta / 2 *
        (Real.sqrt (fab.tailCurrent / fab.beta) + m / 2) ^ 2 ≤
      supply + fab.threshold) :
    ∃ vop von vtail : ℝ → ℝ,
      (∀ d ∈ Set.Ioo (-m) m,
        DiffPairDC fab supply (cm + d / 2) (cm - d / 2)
          (vop d) (von d) (vtail d)) ∧
      HasDerivAt (fun d => vop d - von d)
        (-(fab.drainResistance * fab.beta *
          Real.sqrt (fab.tailCurrent / fab.beta))) 0 := by
  refine ⟨fun d => diffPairOutP fab supply d,
    fun d => diffPairOutN fab supply d,
    fun d => diffPairTail fab cm d, fun d hd => ?_,
    diffPair_transfer_hasDerivAt fab supply hbeta htail⟩
  have habs : |d| < m := abs_lt.mpr ⟨hd.1, hd.2⟩
  exact diffPair_dc_transfer_realizable hbeta hrd htail
    (diffPair_conducting_of_lt habs hcond)
    (diffPair_window_of_lt hbeta hrd habs hwin)

/-! ## Behavior-level pairing (design law: every behavior theorem ships
with a realizability twin) -/

/-- The balanced run window: both gates driven at one common mode inside
the balanced saturation window. -/
def DiffPairBalancedRun (world : DiffPairWorld) : Prop :=
  DiffPairAdmissible world ∧
  world.environment.inputN = world.environment.inputP ∧
  world.environment.inputP +
      world.fabricated.drainResistance *
        world.fabricated.tailCurrent / 2 ≤
    world.environment.supply + world.fabricated.threshold

/-- Specification layer: in every balanced run, both outputs sit at the
derived `V_DD − R_D·I_T/2` and the tail node tracks the common mode. -/
theorem diffPair_balanced_safe :
    SafeUnder DiffPairBehavior DiffPairBalancedRun
      (fun world boundary internal =>
        boundary.outputP = world.environment.supply -
          world.fabricated.drainResistance *
            world.fabricated.tailCurrent / 2 ∧
        boundary.outputN = world.environment.supply -
          world.fabricated.drainResistance *
            world.fabricated.tailCurrent / 2 ∧
        internal.tailVoltage = world.environment.inputP -
          world.fabricated.threshold -
          Real.sqrt (world.fabricated.tailCurrent /
            world.fabricated.beta)) := by
  intro world boundary internal hallowed hbehavior
  obtain ⟨hadmissible, hbal, hwin⟩ := hallowed
  have hdc : DiffPairDC world.fabricated world.environment.supply
      world.environment.inputP world.environment.inputP
      boundary.outputP boundary.outputN internal.tailVoltage := by
    have h := hbehavior
    unfold DiffPairBehavior at h
    rw [hbal] at h
    exact h
  exact diffPair_dc_balanced hadmissible.1 hadmissible.2.2.1
    hadmissible.2.2.2.1 hwin hdc

theorem diffPair_balanced_realizable :
    RealizableUnder DiffPairBehavior DiffPairBalancedRun := by
  intro world hallowed
  obtain ⟨hadmissible, hbal, hwin⟩ := hallowed
  refine ⟨⟨world.environment.supply -
      world.fabricated.drainResistance *
        world.fabricated.tailCurrent / 2,
    world.environment.supply -
      world.fabricated.drainResistance *
        world.fabricated.tailCurrent / 2⟩,
    ⟨world.environment.inputP - world.fabricated.threshold -
      Real.sqrt (world.fabricated.tailCurrent /
        world.fabricated.beta)⟩, ?_⟩
  have h := diffPair_dc_balanced_realizable hadmissible.1
    hadmissible.2.2.1 hadmissible.2.2.2.1 hwin
  unfold DiffPairBehavior
  rw [hbal]
  exact h

/-- The observed output pair is the same in every admitted behavior of an
admissible world. -/
theorem diffPair_determinate :
    DeterminateUnder DiffPairBehavior DiffPairAdmissible (ℝ × ℝ)
      (fun _world boundary _internal =>
        (boundary.outputP, boundary.outputN)) := by
  intro world hadmissible boundary₁ internal₁ boundary₂ internal₂ h₁ h₂
  obtain ⟨hp, hn, -⟩ :=
    diffPair_dc_determinate hadmissible.1 hadmissible.2.2.1
      hadmissible.2.2.2.1 h₁ h₂
  dsimp only
  rw [hp, hn]

/-! ## Evidence layer -/

/-- Provenance record for the ngspice `.op` differential harness on this
pair. Metadata only; it proves nothing by itself. -/
def diffPairHarnessEvidence : EvidenceRecord :=
  { artifact := "harness/spice/amp_test.py"
    artifactHash := ""
    version := "ngspice-46"
    issuer := "spice amp harness"
    modality := .finiteValidation
    domainDescription :=
      "diff_pair.cir .op probes at vdd = 5: balanced (2.5/2.5), common-mode shift (3.5/3.5, outputs invariant), the 3-4-5 large-signal probe (0.85/-0.35), and a central-difference differential-gain probe against the proved derivative -4"
    confidenceDescription :=
      "floating-point agreement within 1e-6 relative at tightened solver tolerances" }

/-- The MOS1-envelope validity claim for the pair: a physical DC relation
for a fabricated part is covered by `DiffPairBehavior` on the balanced
window. Accepting it requires an actual proof or an explicit calibration
hypothesis — the evidence record alone cannot construct
`AcceptedValidity`. -/
def diffPairEnvelopeClaim
    (physical : Behavior DiffPairWorld DiffPairBoundary DiffPairInternal) :
    ValidityClaim DiffPairWorld DiffPairBoundary DiffPairInternal :=
  { physical
    envelope := DiffPairBehavior
    domain := fun world _boundary _internal => DiffPairBalancedRun world }

/-- Pair the harness provenance with an explicit acceptance hypothesis.
Bench calibration later replaces the hypothesis; nothing here is assumed
silently. -/
def diffPairAcceptedValidity
    (physical : Behavior DiffPairWorld DiffPairBoundary DiffPairInternal)
    (haccepted : (diffPairEnvelopeClaim physical).statement) :
    AcceptedValidity (diffPairEnvelopeClaim physical) :=
  { evidence := diffPairHarnessEvidence
    accepted := haccepted }

end LeanModels.Spice

namespace LeanModels.Circuit

/-- Type-namespace wrapper so field notation on the shared parsed circuit
resolves without exposing the SPICE implementation namespace. -/
def ElaboratedCircuit.toDiffPairNominal
    (circuit : ElaboratedCircuit) :
    Except String LeanModels.Spice.DiffPairNominal :=
  LeanModels.Spice.ElaboratedCircuit.toDiffPairNominal circuit

end LeanModels.Circuit
