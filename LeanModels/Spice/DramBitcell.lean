import LeanModels.Spice.Dram1T1C
import LeanModels.Circuit.Equation

/-!
# Charge-sharing DRAM read and parameterized bank

The access transistor and capacitances come from a typed SPICE component.
Read correctness is derived from charge conservation. The sense/restore
stage is a separate relational component, so its ideality is visible in the
assurance boundary rather than hidden in the cell equations.
-/

namespace LeanModels.Spice

open LeanModels.Circuit

structure DramReadNominal where
  storageNode : LeanModels.Circuit.NodeId
  wordlineNode : LeanModels.Circuit.NodeId
  bitlineNode : LeanModels.Circuit.NodeId
  threshold : Rat
  beta : Rat
  storageCapacitance : Rat
  bitlineCapacitance : Rat
deriving Repr, BEq, Inhabited

/-- Recognize a 1T1C cell together with its explicit bitline load. -/
def ElaboratedCircuit.toDramReadNominal
    (circuit : ElaboratedCircuit) : Except String DramReadNominal := do
  if circuit.devices.size != 3 then
    throw s!"DRAM read cell requires three devices, found {circuit.devices.size}"
  let mosfets := circuit.devices.toList.filterMap fun
    | .mosfet _ drain gate source bulk model =>
        some (drain, gate, source, bulk, model)
    | _ => none
  let capacitors := circuit.devices.toList.filterMap fun
    | .capacitor _ positive negative value =>
        some (positive, negative, value)
    | _ => none
  let (storage, wordline, bitline, bulk, modelId) ←
    match mosfets with
    | [mosfet] => pure mosfet
    | _ => throw "DRAM read cell requires exactly one access MOSFET"
  let storageCapacitance ←
    match capacitors.find? fun capacitor =>
        capacitor.1 == storage && capacitor.2.1 == circuit.ground with
    | some capacitor => pure capacitor.2.2
    | none => throw "missing storage capacitor"
  let bitlineCapacitance ←
    match capacitors.find? fun capacitor =>
        capacitor.1 == bitline && capacitor.2.1 == circuit.ground with
    | some capacitor => pure capacitor.2.2
    | none => throw "missing bitline capacitor"
  unless bulk == circuit.ground do
    throw "access-transistor bulk is not grounded"
  let model ← match circuit.models[modelId.index]? with
    | some (.mos1 model) => pure model
    | _ => throw "DRAM access model is missing"
  unless model.polarity == .nmos &&
      model.channelLengthModulation == 0 &&
      model.junctionSaturation == 0 do
    throw "DRAM access device is outside the proved MOS1 profile"
  pure
    { storageNode := storage
      wordlineNode := wordline
      bitlineNode := bitline
      threshold := model.threshold
      beta := model.transconductance
      storageCapacitance
      bitlineCapacitance }

structure DramReadParameters where
  supply : ℝ
  storageCapacitance : ℝ
  bitlineCapacitance : ℝ
  precharge : ℝ

def DramReadAdmissible (parameter : DramReadParameters) : Prop :=
  0 < parameter.supply ∧
  0 < parameter.storageCapacitance ∧
  0 < parameter.bitlineCapacitance ∧
  parameter.precharge = parameter.supply / 2

noncomputable def dramStoredVoltage
    (parameter : DramReadParameters) (stored : Bool) : ℝ :=
  if stored then parameter.supply else 0

/-- Final voltage after ideal wordline connection, derived by conserving the
total charge on the storage and bitline capacitors. -/
noncomputable def dramSharedVoltage
    (parameter : DramReadParameters) (stored : Bool) : ℝ :=
  (parameter.storageCapacitance * dramStoredVoltage parameter stored +
      parameter.bitlineCapacitance * parameter.precharge) /
    (parameter.storageCapacitance + parameter.bitlineCapacitance)

def IdealSenseContract
    (parameter : DramReadParameters) (voltage : ℝ) (sensed : Bool) : Prop :=
  (sensed = true ∧ parameter.precharge < voltage) ∨
    (sensed = false ∧ voltage < parameter.precharge)

structure DramReadObservation where
  sharedVoltage : ℝ
  sensed : Bool
  restoredVoltage : ℝ

inductive DramReadClause where
  | chargeSharing
  | idealSense
  | idealRestore
deriving Repr, DecidableEq

noncomputable def DramReadProgram
    (parameter : DramReadParameters) (stored : Bool) :
    EquationProgram DramReadClause Unit DramReadObservation Unit where
  origin
    | .chargeSharing => .connectionLaw "capacitor charge conservation"
    | .idealSense => .importedContract "ideal sense discriminator"
    | .idealRestore => .importedContract "ideal restore endpoint"
  equation clause _world observation _internal :=
    match clause with
    | .chargeSharing =>
        observation.sharedVoltage = dramSharedVoltage parameter stored
    | .idealSense =>
        IdealSenseContract parameter observation.sharedVoltage
          observation.sensed
    | .idealRestore =>
        observation.restoredVoltage =
          dramStoredVoltage parameter observation.sensed

noncomputable def DramReadBehavior
    (parameter : DramReadParameters) (stored : Bool)
    (observation : DramReadObservation) : Prop :=
  (DramReadProgram parameter stored).behavior () observation ()

theorem dramReadEquationManifest :
    EquationManifest
      (DramReadProgram parameter stored)
      ["ideal sense discriminator", "ideal restore endpoint"] := by
  constructor
  · intro contract hcontract
    simp at hcontract
    rcases hcontract with rfl | rfl
    · exact ⟨.idealSense, rfl⟩
    · exact ⟨.idealRestore, rfl⟩
  · intro contract hcontract
    rcases hcontract with ⟨clause, hclause⟩
    cases clause <;>
      simp [DramReadProgram] at hclause ⊢
    all_goals subst contract <;> simp

theorem dram_read_signal
    {parameter : DramReadParameters}
    (hadmissible : DramReadAdmissible parameter) (stored : Bool) :
    dramSharedVoltage parameter stored - parameter.precharge =
      parameter.storageCapacitance *
          (dramStoredVoltage parameter stored - parameter.precharge) /
        (parameter.storageCapacitance + parameter.bitlineCapacitance) := by
  have hsum :
      parameter.storageCapacitance + parameter.bitlineCapacitance ≠ 0 :=
    ne_of_gt (add_pos hadmissible.2.1 hadmissible.2.2.1)
  unfold dramSharedVoltage
  field_simp [hsum]
  ring

theorem dram_read_signal_sign
    {parameter : DramReadParameters}
    (hadmissible : DramReadAdmissible parameter) (stored : Bool) :
    if stored then
      parameter.precharge < dramSharedVoltage parameter stored
    else
      dramSharedVoltage parameter stored < parameter.precharge := by
  have hsum :
      0 < parameter.storageCapacitance +
        parameter.bitlineCapacitance :=
    add_pos hadmissible.2.1 hadmissible.2.2.1
  rcases stored with _ | _
  · simp only [Bool.false_eq_true, ↓reduceIte]
    have hsignal := dram_read_signal hadmissible false
    have hnegative :
        parameter.storageCapacitance *
              (dramStoredVoltage parameter false - parameter.precharge) /
            (parameter.storageCapacitance +
              parameter.bitlineCapacitance) < 0 := by
      apply div_neg_of_neg_of_pos _ hsum
      apply mul_neg_of_pos_of_neg hadmissible.2.1
      simp [dramStoredVoltage, hadmissible.2.2.2]
      linarith [hadmissible.1]
    linarith
  · simp only [↓reduceIte]
    have hsignal := dram_read_signal hadmissible true
    have hpositive :
        0 < parameter.storageCapacitance *
              (dramStoredVoltage parameter true - parameter.precharge) /
            (parameter.storageCapacitance +
              parameter.bitlineCapacitance) := by
      apply div_pos _ hsum
      apply mul_pos hadmissible.2.1
      simp [dramStoredVoltage, hadmissible.2.2.2]
      linarith [hadmissible.1]
    linarith

/-- The charge-sharing signal has a closed-form worst-case sense margin. -/
theorem dram_read_margin
    {parameter : DramReadParameters}
    (hadmissible : DramReadAdmissible parameter) (stored : Bool) :
    |dramSharedVoltage parameter stored - parameter.precharge| =
      parameter.storageCapacitance * parameter.supply /
        (2 * (parameter.storageCapacitance +
          parameter.bitlineCapacitance)) := by
  rcases stored with _ | _
  · rw [dram_read_signal hadmissible]
    have hnegative :
        parameter.storageCapacitance *
              (dramStoredVoltage parameter false - parameter.precharge) /
            (parameter.storageCapacitance +
              parameter.bitlineCapacitance) < 0 := by
      apply div_neg_of_neg_of_pos
      · apply mul_neg_of_pos_of_neg hadmissible.2.1
        simp [dramStoredVoltage, hadmissible.2.2.2]
        linarith [hadmissible.1]
      · exact add_pos hadmissible.2.1 hadmissible.2.2.1
    rw [abs_of_neg hnegative]
    simp [dramStoredVoltage, hadmissible.2.2.2]
    field_simp
  · rw [dram_read_signal hadmissible]
    have hpositive :
        0 < parameter.storageCapacitance *
              (dramStoredVoltage parameter true - parameter.precharge) /
            (parameter.storageCapacitance +
              parameter.bitlineCapacitance) := by
      apply div_pos
      · apply mul_pos hadmissible.2.1
        simp [dramStoredVoltage, hadmissible.2.2.2]
        linarith [hadmissible.1]
      · exact add_pos hadmissible.2.1 hadmissible.2.2.1
    rw [abs_of_pos hpositive]
    simp [dramStoredVoltage, hadmissible.2.2.2]
    field_simp
    ring

theorem dram_read_realizable
    {parameter : DramReadParameters}
    (hadmissible : DramReadAdmissible parameter) (stored : Bool) :
    ∃ observation, DramReadBehavior parameter stored observation := by
  let observation : DramReadObservation :=
    { sharedVoltage := dramSharedVoltage parameter stored
      sensed := stored
      restoredVoltage := dramStoredVoltage parameter stored }
  refine ⟨observation, ?_⟩
  intro clause
  cases clause
  case chargeSharing => rfl
  case idealSense =>
    rcases stored with _ | _
    · exact Or.inr ⟨rfl, dram_read_signal_sign hadmissible false⟩
    · exact Or.inl ⟨rfl, dram_read_signal_sign hadmissible true⟩
  case idealRestore => rfl

/-- Every admissible read returns the stored bit and restores its rail. -/
theorem dram_read_correct
    {parameter : DramReadParameters}
    (hadmissible : DramReadAdmissible parameter)
    {stored : Bool} {observation : DramReadObservation}
    (hbehavior : DramReadBehavior parameter stored observation) :
    observation.sensed = stored ∧
      observation.restoredVoltage =
        dramStoredVoltage parameter stored := by
  have hshared := hbehavior .chargeSharing
  have hsense := hbehavior .idealSense
  have hrestore := hbehavior .idealRestore
  have hsign := dram_read_signal_sign hadmissible stored
  rcases stored with _ | _
  · simp only [Bool.false_eq_true, ↓reduceIte] at hsign
    rcases hsense with ⟨hsensed, hwrong⟩ | ⟨hsensed, _hright⟩
    · have hfalse : False := by
        rw [← hshared] at hsign
        linarith
      exact hfalse.elim
    · exact ⟨hsensed, by
        simpa [DramReadProgram, hsensed] using hrestore⟩
  · simp only [↓reduceIte] at hsign
    rcases hsense with ⟨hsensed, _hright⟩ | ⟨hsensed, hwrong⟩
    · exact ⟨hsensed, by
        simpa [DramReadProgram, hsensed] using hrestore⟩
    · have hfalse : False := by
        rw [← hshared] at hsign
        linarith
      exact hfalse.elim

/-! ## Arbitrary-size bank contract -/

structure DramBankState (width : Nat) where
  bits : Fin width → Bool

def DramBankReadContract
    (parameter : DramReadParameters) {width : Nat}
    (before : DramBankState width) (address : Fin width)
    (output : Bool) (after : DramBankState width) : Prop :=
  ∃ observation,
    DramReadBehavior parameter (before.bits address) observation ∧
    output = observation.sensed ∧ after = before

theorem dram_bank_read_realizable
    {parameter : DramReadParameters}
    (hadmissible : DramReadAdmissible parameter)
    {width : Nat} (before : DramBankState width) (address : Fin width) :
    ∃ output after,
      DramBankReadContract parameter before address output after := by
  obtain ⟨observation, hread⟩ :=
    dram_read_realizable hadmissible (before.bits address)
  exact ⟨observation.sensed, before, observation, hread, rfl, rfl⟩

/-- One cell theorem proves nondestructive reads for every bank width. -/
theorem dram_bank_read_refines
    {parameter : DramReadParameters}
    (hadmissible : DramReadAdmissible parameter)
    {width : Nat} {before : DramBankState width} {address : Fin width}
    {output : Bool} {after : DramBankState width}
    (hread : DramBankReadContract parameter before address output after) :
    output = before.bits address ∧ after = before := by
  rcases hread with ⟨observation, hcell, houtput, hstate⟩
  have hcorrect := dram_read_correct hadmissible hcell
  exact ⟨houtput.trans hcorrect.1, hstate⟩

def DramBankWriteContract {width : Nat}
    (before : DramBankState width) (address : Fin width)
    (input : Bool) (after : DramBankState width) : Prop :=
  after.bits = Function.update before.bits address input

theorem dram_bank_write_refines
    {width : Nat} {before after : DramBankState width}
    {address : Fin width} {input : Bool}
    (hwrite : DramBankWriteContract before address input after) :
    after.bits address = input ∧
      ∀ other, other ≠ address →
        after.bits other = before.bits other := by
  constructor
  · rw [hwrite]
    simp
  · intro other hne
    rw [hwrite]
    simp [hne]

end LeanModels.Spice

namespace LeanModels.Circuit

def ElaboratedCircuit.toDramReadNominal
    (circuit : ElaboratedCircuit) :
    Except String LeanModels.Spice.DramReadNominal :=
  LeanModels.Spice.ElaboratedCircuit.toDramReadNominal circuit

end LeanModels.Circuit
