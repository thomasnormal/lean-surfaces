import LeanModels.Spice.DramArrayContract

/-!
# Checked complete 2x2 DRAM bank deck

The adapter recognizes the entire flattened transistor topology of the
repository bank deck.  Downstream proofs receive typed nodes and devices only
after every capacitor, MOS terminal, model reference, and external port has
matched this source boundary.
-/

namespace LeanModels.Spice

open LeanModels.Circuit

structure DramBank2x2Layout where
  array : DramArrayLayout 2 2
  supply : LeanModels.Circuit.NodeId
  prechargeReference : LeanModels.Circuit.NodeId
  activate : LeanModels.Circuit.NodeId
  row : LeanModels.Circuit.NodeId
  rowBar : LeanModels.Circuit.NodeId
  column : LeanModels.Circuit.NodeId
  columnBar : LeanModels.Circuit.NodeId
  precharge : LeanModels.Circuit.NodeId
  write : LeanModels.Circuit.NodeId
  writeBar : LeanModels.Circuit.NodeId
  restore : LeanModels.Circuit.NodeId
  restoreBar : LeanModels.Circuit.NodeId
  dataIn : LeanModels.Circuit.NodeId
  dataOut : LeanModels.Circuit.NodeId
  senseIntermediate : Fin 2 → LeanModels.Circuit.NodeId
  senseOutput : Fin 2 → LeanModels.Circuit.NodeId
  writeBus : LeanModels.Circuit.NodeId
  prechargeDevices : Fin 2 → DeviceId
  readMuxNmos : Fin 2 → DeviceId
  readMuxPmos : Fin 2 → DeviceId
  writeMuxNmos : Fin 2 → DeviceId
  writeMuxPmos : Fin 2 → DeviceId
  writeNmos : DeviceId
  writePmos : DeviceId
  restoreNmos : Fin 2 → DeviceId
  restorePmos : Fin 2 → DeviceId
  sensePmos : Fin 2 → Fin 2 → DeviceId
  senseNmos : Fin 2 → Fin 2 → DeviceId
  pThreshold : Rat
  pBeta : Rat
  sensePThreshold : Rat
  sensePBeta : Rat
deriving Inhabited

def matchesCapacitor
    (circuit : ElaboratedCircuit) (index : Nat)
    (positive negative : LeanModels.Circuit.NodeId)
    (capacitance : Rat) : Bool :=
  match circuit.devices[index]? with
  | some (.capacitor id actualPositive actualNegative actualCapacitance) =>
      id.index == index && actualPositive == positive &&
        actualNegative == negative && actualCapacitance == capacitance
  | _ => false

def matchesMosfet
    (circuit : ElaboratedCircuit) (index : Nat)
    (drain gate source bulk : LeanModels.Circuit.NodeId)
    (model : LeanModels.Circuit.ModelId) : Bool :=
  match circuit.devices[index]? with
  | some (.mosfet id actualDrain actualGate actualSource actualBulk actualModel) =>
      id.index == index && actualDrain == drain && actualGate == gate &&
        actualSource == source && actualBulk == bulk &&
        actualModel == model
  | _ => false

def matchesMos1Model
    (circuit : ElaboratedCircuit) (index : Nat)
    (polarity : MosPolarity) (threshold beta : Rat) : Bool :=
  match circuit.models[index]? with
  | some (.mos1 model) =>
      model.id.index == index && model.polarity == polarity &&
        model.threshold == threshold &&
        model.transconductance == beta &&
        model.channelLengthModulation == 0 &&
        model.junctionSaturation == 0
  | _ => false

def dramBank2x2NamesMatch (circuit : ElaboratedCircuit) : Bool :=
  circuit.nodeNames == #[
    "xbank.bit0", "0", "xbank.bit1", "xbank.store00",
    "xbank.store01", "xbank.store10", "xbank.store11", "precharge",
    "vpre", "xbank.xword0.nand", "activate", "vdd", "rowb",
    "xbank.xword0.nseries", "xbank.word0", "xbank.xword1.nand",
    "row", "xbank.xword1.nseries", "xbank.word1", "xbank.sensed0_n",
    "xbank.sensed0", "xbank.sensed1_n", "xbank.sensed1", "restore",
    "restoreb", "colb", "dout", "col", "din", "write",
    "xbank.writebus", "writeb"] &&
  circuit.deviceNames == #[
    "xbank.cbit0", "xbank.cbit1", "xbank.xcell00.cstore",
    "xbank.xcell01.cstore", "xbank.xcell10.cstore",
    "xbank.xcell11.cstore", "xbank.mpre0", "xbank.mpre1",
    "xbank.xword0.mpa", "xbank.xword0.mpb", "xbank.xword0.mna",
    "xbank.xword0.mnb", "xbank.xword0.mpinv", "xbank.xword0.mninv",
    "xbank.xword1.mpa", "xbank.xword1.mpb", "xbank.xword1.mna",
    "xbank.xword1.mnb", "xbank.xword1.mpinv", "xbank.xword1.mninv",
    "xbank.xcell00.maccess", "xbank.xcell01.maccess",
    "xbank.xcell10.maccess", "xbank.xcell11.maccess",
    "xbank.xsense00.mp", "xbank.xsense00.mn",
    "xbank.xsense01.mp", "xbank.xsense01.mn",
    "xbank.xsense10.mp", "xbank.xsense10.mn",
    "xbank.xsense11.mp", "xbank.xsense11.mn",
    "xbank.xrestore0.mn", "xbank.xrestore0.mp",
    "xbank.xrestore1.mn", "xbank.xrestore1.mp",
    "xbank.xreadmux0.mn", "xbank.xreadmux0.mp",
    "xbank.xreadmux1.mn", "xbank.xreadmux1.mp",
    "xbank.xwrite.mn", "xbank.xwrite.mp",
    "xbank.xwritemux0.mn", "xbank.xwritemux0.mp",
    "xbank.xwritemux1.mn", "xbank.xwritemux1.mp"] &&
  circuit.modelNames == #["nmod", "pmod", "psense"]

def dramBank2x2TopologyMatches (circuit : ElaboratedCircuit) : Bool :=
  dramBank2x2NamesMatch circuit &&
  circuit.ground == ⟨1⟩ &&
  matchesCapacitor circuit 0 ⟨0⟩ ⟨1⟩ (3 / 10000000000000) &&
  matchesCapacitor circuit 1 ⟨2⟩ ⟨1⟩ (3 / 10000000000000) &&
  matchesCapacitor circuit 2 ⟨3⟩ ⟨1⟩ (3 / 100000000000000) &&
  matchesCapacitor circuit 3 ⟨4⟩ ⟨1⟩ (3 / 100000000000000) &&
  matchesCapacitor circuit 4 ⟨5⟩ ⟨1⟩ (3 / 100000000000000) &&
  matchesCapacitor circuit 5 ⟨6⟩ ⟨1⟩ (3 / 100000000000000) &&
  matchesMosfet circuit 6 ⟨0⟩ ⟨7⟩ ⟨8⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 7 ⟨2⟩ ⟨7⟩ ⟨8⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 8 ⟨9⟩ ⟨10⟩ ⟨11⟩ ⟨11⟩ ⟨1⟩ &&
  matchesMosfet circuit 9 ⟨9⟩ ⟨12⟩ ⟨11⟩ ⟨11⟩ ⟨1⟩ &&
  matchesMosfet circuit 10 ⟨9⟩ ⟨10⟩ ⟨13⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 11 ⟨13⟩ ⟨12⟩ ⟨1⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 12 ⟨14⟩ ⟨9⟩ ⟨11⟩ ⟨11⟩ ⟨1⟩ &&
  matchesMosfet circuit 13 ⟨14⟩ ⟨9⟩ ⟨1⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 14 ⟨15⟩ ⟨10⟩ ⟨11⟩ ⟨11⟩ ⟨1⟩ &&
  matchesMosfet circuit 15 ⟨15⟩ ⟨16⟩ ⟨11⟩ ⟨11⟩ ⟨1⟩ &&
  matchesMosfet circuit 16 ⟨15⟩ ⟨10⟩ ⟨17⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 17 ⟨17⟩ ⟨16⟩ ⟨1⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 18 ⟨18⟩ ⟨15⟩ ⟨11⟩ ⟨11⟩ ⟨1⟩ &&
  matchesMosfet circuit 19 ⟨18⟩ ⟨15⟩ ⟨1⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 20 ⟨3⟩ ⟨14⟩ ⟨0⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 21 ⟨4⟩ ⟨14⟩ ⟨2⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 22 ⟨5⟩ ⟨18⟩ ⟨0⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 23 ⟨6⟩ ⟨18⟩ ⟨2⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 24 ⟨19⟩ ⟨0⟩ ⟨11⟩ ⟨11⟩ ⟨2⟩ &&
  matchesMosfet circuit 25 ⟨19⟩ ⟨0⟩ ⟨1⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 26 ⟨20⟩ ⟨19⟩ ⟨11⟩ ⟨11⟩ ⟨2⟩ &&
  matchesMosfet circuit 27 ⟨20⟩ ⟨19⟩ ⟨1⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 28 ⟨21⟩ ⟨2⟩ ⟨11⟩ ⟨11⟩ ⟨2⟩ &&
  matchesMosfet circuit 29 ⟨21⟩ ⟨2⟩ ⟨1⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 30 ⟨22⟩ ⟨21⟩ ⟨11⟩ ⟨11⟩ ⟨2⟩ &&
  matchesMosfet circuit 31 ⟨22⟩ ⟨21⟩ ⟨1⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 32 ⟨20⟩ ⟨23⟩ ⟨0⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 33 ⟨20⟩ ⟨24⟩ ⟨0⟩ ⟨11⟩ ⟨1⟩ &&
  matchesMosfet circuit 34 ⟨22⟩ ⟨23⟩ ⟨2⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 35 ⟨22⟩ ⟨24⟩ ⟨2⟩ ⟨11⟩ ⟨1⟩ &&
  matchesMosfet circuit 36 ⟨20⟩ ⟨25⟩ ⟨26⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 37 ⟨20⟩ ⟨27⟩ ⟨26⟩ ⟨11⟩ ⟨1⟩ &&
  matchesMosfet circuit 38 ⟨22⟩ ⟨27⟩ ⟨26⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 39 ⟨22⟩ ⟨25⟩ ⟨26⟩ ⟨11⟩ ⟨1⟩ &&
  matchesMosfet circuit 40 ⟨28⟩ ⟨29⟩ ⟨30⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 41 ⟨28⟩ ⟨31⟩ ⟨30⟩ ⟨11⟩ ⟨1⟩ &&
  matchesMosfet circuit 42 ⟨30⟩ ⟨25⟩ ⟨0⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 43 ⟨30⟩ ⟨27⟩ ⟨0⟩ ⟨11⟩ ⟨1⟩ &&
  matchesMosfet circuit 44 ⟨30⟩ ⟨27⟩ ⟨2⟩ ⟨1⟩ ⟨0⟩ &&
  matchesMosfet circuit 45 ⟨30⟩ ⟨25⟩ ⟨2⟩ ⟨11⟩ ⟨1⟩ &&
  matchesMos1Model circuit 0 .nmos 1 (1 / 10000) &&
  matchesMos1Model circuit 1 .pmos 1 (1 / 20000) &&
  matchesMos1Model circuit 2 .pmos 1 (1 / 10000)

def checkedDramBank2x2Layout : DramBank2x2Layout :=
  let cell00 : DramCellLayout :=
    ⟨⟨20⟩, ⟨2⟩, ⟨3⟩, ⟨14⟩, ⟨0⟩, ⟨0⟩,
      3 / 100000000000000⟩
  let cell01 : DramCellLayout :=
    ⟨⟨21⟩, ⟨3⟩, ⟨4⟩, ⟨14⟩, ⟨2⟩, ⟨0⟩,
      3 / 100000000000000⟩
  let cell10 : DramCellLayout :=
    ⟨⟨22⟩, ⟨4⟩, ⟨5⟩, ⟨18⟩, ⟨0⟩, ⟨0⟩,
      3 / 100000000000000⟩
  let cell11 : DramCellLayout :=
    ⟨⟨23⟩, ⟨5⟩, ⟨6⟩, ⟨18⟩, ⟨2⟩, ⟨0⟩,
      3 / 100000000000000⟩
  { array :=
      { cells := fun row column =>
          selectFin2
            (selectFin2 cell00 cell01 column)
            (selectFin2 cell10 cell11 column) row
        wordlines := selectFin2 ⟨14⟩ ⟨18⟩
        bitlines := selectFin2 ⟨0⟩ ⟨2⟩
        bitlineCapacitors := selectFin2 ⟨0⟩ ⟨1⟩
        bitlineCapacitances :=
          selectFin2 (3 / 10000000000000) (3 / 10000000000000)
        threshold := 1
        beta := 1 / 10000 }
    supply := ⟨11⟩
    prechargeReference := ⟨8⟩
    activate := ⟨10⟩
    row := ⟨16⟩
    rowBar := ⟨12⟩
    column := ⟨27⟩
    columnBar := ⟨25⟩
    precharge := ⟨7⟩
    write := ⟨29⟩
    writeBar := ⟨31⟩
    restore := ⟨23⟩
    restoreBar := ⟨24⟩
    dataIn := ⟨28⟩
    dataOut := ⟨26⟩
    senseIntermediate := selectFin2 ⟨19⟩ ⟨21⟩
    senseOutput := selectFin2 ⟨20⟩ ⟨22⟩
    writeBus := ⟨30⟩
    prechargeDevices := selectFin2 ⟨6⟩ ⟨7⟩
    readMuxNmos := selectFin2 ⟨36⟩ ⟨38⟩
    readMuxPmos := selectFin2 ⟨37⟩ ⟨39⟩
    writeMuxNmos := selectFin2 ⟨42⟩ ⟨44⟩
    writeMuxPmos := selectFin2 ⟨43⟩ ⟨45⟩
    writeNmos := ⟨40⟩
    writePmos := ⟨41⟩
    restoreNmos := selectFin2 ⟨32⟩ ⟨34⟩
    restorePmos := selectFin2 ⟨33⟩ ⟨35⟩
    sensePmos := fun column stage =>
      selectFin2
        (selectFin2 ⟨24⟩ ⟨26⟩ stage)
        (selectFin2 ⟨28⟩ ⟨30⟩ stage) column
    senseNmos := fun column stage =>
      selectFin2
        (selectFin2 ⟨25⟩ ⟨27⟩ stage)
        (selectFin2 ⟨29⟩ ⟨31⟩ stage) column
    pThreshold := 1
    pBeta := 1 / 20000
    sensePThreshold := 1
    sensePBeta := 1 / 10000 }

def ElaboratedCircuit.toDramBank2x2
    (circuit : ElaboratedCircuit) : Except String DramBank2x2Layout :=
  if dramBank2x2TopologyMatches circuit then
    .ok checkedDramBank2x2Layout
  else
    .error "circuit does not match the checked transistor-level 2x2 DRAM bank"

end LeanModels.Spice

namespace LeanModels.Circuit

def ElaboratedCircuit.toDramBank2x2
    (circuit : ElaboratedCircuit) :
    Except String LeanModels.Spice.DramBank2x2Layout :=
  LeanModels.Spice.ElaboratedCircuit.toDramBank2x2 circuit

end LeanModels.Circuit
