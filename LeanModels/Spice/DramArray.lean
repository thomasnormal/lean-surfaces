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

/-- Recognize exactly four 1T1C cells in a 2x2 shared-row/shared-column
topology plus one explicit load capacitor per bitline. -/
def ElaboratedCircuit.toDramArray2x2
    (circuit : ElaboratedCircuit) :
    Except String (DramArrayLayout 2 2) :=
  match circuit.deviceNames.toList, circuit.modelNames.toList,
      circuit.devices.toList, circuit.models.toList with
  | ["cbit0", "cbit1",
      "xcell00.cstore", "xcell01.cstore",
      "xcell10.cstore", "xcell11.cstore",
      "xcell00.maccess", "xcell01.maccess",
      "xcell10.maccess", "xcell11.maccess"],
    ["nmod"],
    [.capacitor bitCap0 bit0 bitGround0 bitCapacitance0,
      .capacitor bitCap1 bit1 bitGround1 bitCapacitance1,
      .capacitor storeCap00 store00 storeGround00 storageCapacitance00,
      .capacitor storeCap01 store01 storeGround01 storageCapacitance01,
      .capacitor storeCap10 store10 storeGround10 storageCapacitance10,
      .capacitor storeCap11 store11 storeGround11 storageCapacitance11,
      .mosfet access00 drain00 word0 source00 bulk00 model00,
      .mosfet access01 drain01 word01 source01 bulk01 model01,
      .mosfet access10 drain10 word1 source10 bulk10 model10,
      .mosfet access11 drain11 word11 source11 bulk11 model11],
    [.mos1 model] =>
      if bitGround0 == circuit.ground &&
          bitGround1 == circuit.ground &&
          storeGround00 == circuit.ground &&
          storeGround01 == circuit.ground &&
          storeGround10 == circuit.ground &&
          storeGround11 == circuit.ground &&
          bulk00 == circuit.ground &&
          bulk01 == circuit.ground &&
          bulk10 == circuit.ground &&
          bulk11 == circuit.ground &&
          drain00 == store00 && drain01 == store01 &&
          drain10 == store10 && drain11 == store11 &&
          word0 == word01 && word1 == word11 && word0 != word1 &&
          source00 == bit0 && source10 == bit0 &&
          source01 == bit1 && source11 == bit1 && bit0 != bit1 &&
          model00 == model.id && model01 == model.id &&
          model10 == model.id && model11 == model.id &&
          storageCapacitance00 == storageCapacitance01 &&
          storageCapacitance00 == storageCapacitance10 &&
          storageCapacitance00 == storageCapacitance11 &&
          0 < storageCapacitance00 &&
          0 < bitCapacitance0 && 0 < bitCapacitance1 &&
          model.polarity == .nmos &&
          model.channelLengthModulation == 0 &&
          model.junctionSaturation == 0 &&
          0 < model.threshold && 0 < model.transconductance then
        let cell00 : DramCellLayout :=
          ⟨access00, storeCap00, store00, word0, bit0,
            model.id, storageCapacitance00⟩
        let cell01 : DramCellLayout :=
          ⟨access01, storeCap01, store01, word0, bit1,
            model.id, storageCapacitance01⟩
        let cell10 : DramCellLayout :=
          ⟨access10, storeCap10, store10, word1, bit0,
            model.id, storageCapacitance10⟩
        let cell11 : DramCellLayout :=
          ⟨access11, storeCap11, store11, word1, bit1,
            model.id, storageCapacitance11⟩
        .ok
          { cells := fun row column =>
              selectFin2
                (selectFin2 cell00 cell01 column)
                (selectFin2 cell10 cell11 column)
                row
            wordlines := selectFin2 word0 word1
            bitlines := selectFin2 bit0 bit1
            bitlineCapacitors := selectFin2 bitCap0 bitCap1
            bitlineCapacitances :=
              selectFin2 bitCapacitance0 bitCapacitance1
            threshold := model.threshold
            beta := model.transconductance }
      else
        .error "2x2 DRAM array is outside the checked topology or MOS1 profile"
  | _, _, _, _ =>
      .error "2x2 DRAM array does not have the required source topology"

end LeanModels.Spice

namespace LeanModels.Circuit

def ElaboratedCircuit.toDramArray2x2
    (circuit : ElaboratedCircuit) :
    Except String (LeanModels.Spice.DramArrayLayout 2 2) :=
  LeanModels.Spice.ElaboratedCircuit.toDramArray2x2 circuit

end LeanModels.Circuit
