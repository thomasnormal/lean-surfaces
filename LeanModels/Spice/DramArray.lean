import LeanModels.Spice.DramBank
import LeanModels.Spice.Mos1

/-!
# Source-backed DRAM array layouts

The checked adapter below is deliberately stricter than a name lookup.  It
recognizes the complete open 2x2 topology, derives every node and parameter
from the elaborated `.cir` artifact, and rejects extra or miswired devices.
-/

namespace LeanModels.Spice

open LeanModels.Circuit

structure DramCellLayout where
  accessDevice : DeviceId
  storageCapacitor : DeviceId
  storageNode : LeanModels.Circuit.NodeId
  wordlineNode : LeanModels.Circuit.NodeId
  bitlineNode : LeanModels.Circuit.NodeId
  model : LeanModels.Circuit.ModelId
  storageCapacitance : Rat
deriving Repr, BEq, Inhabited

structure DramArrayLayout (rows columns : Nat) where
  cells : Fin rows → Fin columns → DramCellLayout
  wordlines : Fin rows → LeanModels.Circuit.NodeId
  bitlines : Fin columns → LeanModels.Circuit.NodeId
  bitlineCapacitors : Fin columns → DeviceId
  bitlineCapacitances : Fin columns → Rat
  threshold : Rat
  beta : Rat
deriving Inhabited

def selectFin2 (zero one : α) (index : Fin 2) : α :=
  if index.val = 0 then zero else one

@[simp] theorem selectFin2_zero (zero one : α) :
    selectFin2 zero one (0 : Fin 2) = zero := by
  simp [selectFin2]

@[simp] theorem selectFin2_one (zero one : α) :
    selectFin2 zero one (1 : Fin 2) = one := by
  simp [selectFin2]

private def requireDevice
    (circuit : ElaboratedCircuit) (name : String) :
    Except String (DeviceId × ElaboratedDevice) := do
  let id ← match circuit.device? name with
    | some id => pure id
    | none => throw s!"missing DRAM device `{name}`"
  let device ← match circuit.devices[id.index]? with
    | some device => pure device
    | none => throw s!"invalid typed ID for DRAM device `{name}`"
  pure (id, device)

private def extractCell
    (circuit : ElaboratedCircuit)
    (accessName capacitorName : String) :
    Except String DramCellLayout := do
  let (accessId, access) ← requireDevice circuit accessName
  let (capacitorId, capacitor) ← requireDevice circuit capacitorName
  let (storage, wordline, bitline, bulk, model) ← match access with
    | .mosfet _ drain gate source bulk model =>
        pure (drain, gate, source, bulk, model)
    | _ => throw s!"`{accessName}` is not a MOS access device"
  let (capacitorStorage, capacitorGround, capacitance) ← match capacitor with
    | .capacitor _ positive negative capacitance =>
        pure (positive, negative, capacitance)
    | _ => throw s!"`{capacitorName}` is not a storage capacitor"
  unless bulk == circuit.ground &&
      capacitorStorage == storage &&
      capacitorGround == circuit.ground do
    throw s!"cell `{accessName}` has invalid storage or bulk connectivity"
  unless 0 < capacitance do
    throw s!"cell `{accessName}` has nonpositive storage capacitance"
  pure
    { accessDevice := accessId
      storageCapacitor := capacitorId
      storageNode := storage
      wordlineNode := wordline
      bitlineNode := bitline
      model
      storageCapacitance := capacitance }

private def extractBitlineLoad
    (circuit : ElaboratedCircuit) (name : String) :
    Except String (DeviceId × LeanModels.Circuit.NodeId × Rat) := do
  let (id, device) ← requireDevice circuit name
  match device with
  | .capacitor _ positive negative capacitance =>
      unless negative == circuit.ground do
        throw s!"bitline load `{name}` is not ground referenced"
      unless 0 < capacitance do
        throw s!"bitline load `{name}` has nonpositive capacitance"
      pure (id, positive, capacitance)
  | _ => throw s!"`{name}` is not a bitline capacitor"

/-- Recognize exactly four 1T1C cells in a 2x2 shared-row/shared-column
topology plus one explicit load capacitor per bitline. -/
def ElaboratedCircuit.toDramArray2x2
    (circuit : ElaboratedCircuit) :
    Except String (DramArrayLayout 2 2) := do
  unless circuit.devices.size == 10 do
    throw s!"2x2 DRAM array requires ten devices, found {circuit.devices.size}"
  unless circuit.models.size == 1 do
    throw s!"2x2 DRAM array requires one MOS model, found {circuit.models.size}"
  let cell00 ← extractCell circuit "xcell00.maccess" "xcell00.cstore"
  let cell01 ← extractCell circuit "xcell01.maccess" "xcell01.cstore"
  let cell10 ← extractCell circuit "xcell10.maccess" "xcell10.cstore"
  let cell11 ← extractCell circuit "xcell11.maccess" "xcell11.cstore"
  let (bitCap0, bit0, bitCapacitance0) ←
    extractBitlineLoad circuit "cbit0"
  let (bitCap1, bit1, bitCapacitance1) ←
    extractBitlineLoad circuit "cbit1"
  unless cell00.wordlineNode == cell01.wordlineNode &&
      cell10.wordlineNode == cell11.wordlineNode &&
      cell00.wordlineNode != cell10.wordlineNode do
    throw "2x2 DRAM cells do not share exactly two distinct wordlines"
  unless cell00.bitlineNode == bit0 && cell10.bitlineNode == bit0 &&
      cell01.bitlineNode == bit1 && cell11.bitlineNode == bit1 &&
      bit0 != bit1 do
    throw "2x2 DRAM cells do not share exactly two loaded bitlines"
  unless cell00.model == cell01.model && cell00.model == cell10.model &&
      cell00.model == cell11.model do
    throw "2x2 DRAM cells do not share one MOS model"
  unless cell00.storageCapacitance == cell01.storageCapacitance &&
      cell00.storageCapacitance == cell10.storageCapacitance &&
      cell00.storageCapacitance == cell11.storageCapacitance do
    throw "2x2 DRAM cells do not share one storage-capacitance profile"
  let model ← match circuit.models[cell00.model.index]? with
    | some (.mos1 model) => pure model
    | _ => throw "2x2 DRAM access model is missing"
  unless model.polarity == .nmos &&
      model.channelLengthModulation == 0 &&
      model.junctionSaturation == 0 &&
      0 < model.threshold && 0 < model.transconductance do
    throw "2x2 DRAM array is outside the proved bidirectional MOS1 profile"
  pure
    { cells := fun row column =>
        selectFin2
          (selectFin2 cell00 cell01 column)
          (selectFin2 cell10 cell11 column)
          row
      wordlines :=
        selectFin2 cell00.wordlineNode cell10.wordlineNode
      bitlines := selectFin2 bit0 bit1
      bitlineCapacitors := selectFin2 bitCap0 bitCap1
      bitlineCapacitances :=
        selectFin2 bitCapacitance0 bitCapacitance1
      threshold := model.threshold
      beta := model.transconductance }

end LeanModels.Spice

namespace LeanModels.Circuit

def ElaboratedCircuit.toDramArray2x2
    (circuit : ElaboratedCircuit) :
    Except String (LeanModels.Spice.DramArrayLayout 2 2) :=
  LeanModels.Spice.ElaboratedCircuit.toDramArray2x2 circuit

end LeanModels.Circuit
