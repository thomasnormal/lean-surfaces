import LeanModels.Circuit.Surface
import LeanModels.Spice.DramBankCore
import LeanModels.Spice.DramDifferentialSense
import LeanModels.Spice.DramSenseCoupling

/-!
# Source-derived hierarchical DRAM-bank projection

The projector recognizes the repository's hierarchical DRAM-bank topology for
arbitrary positive row and column counts.  Unlike the former 256x32-specific
adapter, it constructs every semantic parameter from the parsed source:

* access threshold and transconductance come from the referenced NMOS model;
* storage capacitance comes from the reusable cell subcircuit;
* each column's bitline capacitance comes from the bank subcircuit; and
* PMOS and sense-model parameters come from their source model cards.

The concrete example embeds its parsed `SourceCircuit` as a Lean term and
proves that this function reduces to its checked artifact.  A parameter edit
therefore changes the projected profile and cannot be hidden by updating a
separate Boolean matcher.
-/

namespace LeanModels.Spice

open LeanModels.Circuit
open LeanModels.Circuit.Spice

def dramBank256Rows : Nat := 256
def dramBank256Columns : Nat := 32

@[reducible] def dramBankBasePorts : Array String :=
  #["vdd", "vpre", "precharge", "restore", "restoreb",
    "sensehi", "senselo", "write", "writeb", "din", "dout"]

@[reducible] def sourceSubcircuit?
    (source : SourceCircuit) (name : String) : Option SourceSubcircuit :=
  source.subcircuits.find? fun subcircuit => subcircuit.name == name

@[reducible] def sourceModel?
    (source : SourceCircuit) (name : String) : Option SourceMosModel :=
  source.models.find? fun model => model.name == name

@[reducible] def optionToExcept
    (value : Option α) (message : String) : Except String α :=
  match value with
  | some value => .ok value
  | none => .error message

@[reducible] def matchesSourceMosfet
    (mosfet : SourceMosfet)
    (drain gate source bulk model : String) : Bool :=
  mosfet.drain == drain && mosfet.gate == gate &&
    mosfet.source == source && mosfet.bulk == bulk &&
    mosfet.model == model

@[reducible] def matchesSourceInstance
    (item : SourceInstance) (subcircuit : String)
    (connections : Array String) : Bool :=
  item.subcircuit == subcircuit && item.connections == connections

@[reducible] def validSourceModel
    (model : SourceMosModel) (name : String)
    (polarity : SourceMosPolarity) : Bool :=
  let polarityMatches :=
    match model.polarity, polarity with
    | .nmos, .nmos | .pmos, .pmos => true
    | _, _ => false
  let thresholdSign :=
    match polarity with
    | .nmos => 0 < model.threshold
    | .pmos => model.threshold < 0
  model.name == name && polarityMatches && model.level == 1 &&
    thresholdSign && 0 < model.transconductance &&
    model.channelLengthModulation == 0 &&
    model.junctionSaturation == 0

@[reducible] def matchesDramSenseAmplifier
    (subcircuit : SourceSubcircuit) : Bool :=
  subcircuit.name == "dram_sense_amp" &&
    subcircuit.ports == #["q", "qb", "sensehi", "senselo"] &&
    subcircuit.devices.size == 2 &&
    subcircuit.instances.isEmpty &&
    subcircuit.mosfets.size == 4 &&
    (match subcircuit.devices[0]?, subcircuit.devices[1]?,
        subcircuit.mosfets[0]?, subcircuit.mosfets[1]?,
        subcircuit.mosfets[2]?, subcircuit.mosfets[3]? with
    | some trueCapacitor, some complementCapacitor,
        some truePmos, some trueNmos,
        some complementPmos, some complementNmos =>
        (match trueCapacitor.kind, complementCapacitor.kind with
        | .capacitor, .capacitor => true
        | _, _ => false) &&
        trueCapacitor.name == "cq" &&
        trueCapacitor.positive == "q" &&
        trueCapacitor.negative == "0" &&
        0 < trueCapacitor.value &&
        complementCapacitor.name == "cqb" &&
        complementCapacitor.positive == "qb" &&
        complementCapacitor.negative == "0" &&
        0 < complementCapacitor.value &&
        matchesSourceMosfet truePmos
          "q" "qb" "sensehi" "sensehi" "psense" &&
        matchesSourceMosfet trueNmos
          "q" "qb" "senselo" "senselo" "nmod" &&
        matchesSourceMosfet complementPmos
          "qb" "q" "sensehi" "sensehi" "psense" &&
        matchesSourceMosfet complementNmos
          "qb" "q" "senselo" "senselo" "nmod"
    | _, _, _, _, _, _ => false)

@[reducible] def matchesTransmissionGate
    (subcircuit : SourceSubcircuit) : Bool :=
  subcircuit.name == "tg" &&
    subcircuit.ports == #["left", "right", "enable", "enableb", "vdd"] &&
    subcircuit.devices.isEmpty &&
    subcircuit.instances.isEmpty &&
    subcircuit.mosfets.size == 2 &&
    (match subcircuit.mosfets[0]?, subcircuit.mosfets[1]? with
    | some nmos, some pmos =>
        matchesSourceMosfet nmos
          "left" "enable" "right" "0" "nmod" &&
        matchesSourceMosfet pmos
          "left" "enableb" "right" "vdd" "pmod"
    | _, _ => false)

@[reducible] def matchesDramCell
    (subcircuit : SourceSubcircuit) : Bool :=
  subcircuit.name == "dram_cell" &&
    subcircuit.ports == #["store", "word", "bit"] &&
    subcircuit.devices.size == 1 &&
    subcircuit.mosfets.size == 1 &&
    subcircuit.instances.isEmpty &&
    (match subcircuit.devices[0]?, subcircuit.mosfets[0]? with
    | some capacitor, some access =>
        (match capacitor.kind with
        | .capacitor => true
        | _ => false) &&
        capacitor.positive == "store" && capacitor.negative == "0" &&
        0 < capacitor.value &&
        matchesSourceMosfet access
          "store" "word" "bit" "0" "nmod"
    | _, _ => false)

@[reducible] def dramRowStorageNames
    (subcircuit : SourceSubcircuit) : Array String :=
  subcircuit.instances.map fun item =>
    item.connections[0]?.getD ""

@[reducible] def dramRowName (columns : Nat) : String :=
  s!"dram_row{columns}"

def dramBankSubarrayRows : Nat := 16

@[reducible] def dramBankSubarrayCount (rows : Nat) : Nat :=
  rows / dramBankSubarrayRows

@[reducible] def dramSubarrayName (columns : Nat) : String :=
  s!"dram_subarray{dramBankSubarrayRows}x{columns}"

@[reducible] def dramBankName (rows columns : Nat) : String :=
  s!"dram_bank_{rows}x{columns}"

@[reducible] def matchesDramRow
    (columns : Nat) (subcircuit : SourceSubcircuit) : Bool :=
  subcircuit.name == dramRowName columns &&
    subcircuit.ports.size == columns + 1 &&
    subcircuit.ports[0]? == some "word" &&
    subcircuit.devices.isEmpty &&
    subcircuit.mosfets.isEmpty &&
    subcircuit.instances.size == columns &&
    (List.range columns).all fun column =>
      match subcircuit.instances[column]?,
          subcircuit.ports[column + 1]? with
      | some item, some bitline =>
          bitline == s!"bit{column}" &&
            item.name == s!"xcell{column}" &&
            item.subcircuit == "dram_cell" &&
            item.connections.size == 3 &&
            item.connections[0]? == some s!"store{column}" &&
            item.connections[1]? == some "word" &&
            item.connections[2]? == some bitline
      | _, _ => false

@[reducible] def dramBankBitlines (columns : Nat) : Array String :=
  ((List.range columns).map fun column => s!"bit{column}").toArray

@[reducible] def matchesDramSubarrayRow
    (columns : Nat) (subcircuit : SourceSubcircuit)
    (row : Nat) : Bool :=
  match subcircuit.instances[row]?,
      subcircuit.ports[row]? with
  | some item, some wordline =>
      wordline == s!"word{row}" &&
        item.name == s!"xrow{row}" &&
        matchesSourceInstance item (dramRowName columns)
        (#[wordline] ++
          (subcircuit.ports.toList.drop
            dramBankSubarrayRows).toArray)
  | _, _ => false

@[reducible] def matchesDramSubarray
    (columns : Nat) (subcircuit : SourceSubcircuit) : Bool :=
  subcircuit.name == dramSubarrayName columns &&
    subcircuit.ports.size == dramBankSubarrayRows + columns &&
    subcircuit.devices.isEmpty &&
    subcircuit.mosfets.isEmpty &&
    subcircuit.instances.size == dramBankSubarrayRows &&
    (List.range dramBankSubarrayRows).all
      (matchesDramSubarrayRow columns subcircuit)

@[reducible] def dramBankSubarrayConnections
    (columns subarray : Nat) :
    Array String :=
  let wordlines :=
    ((List.range dramBankSubarrayRows).map fun offset =>
      s!"word{subarray * dramBankSubarrayRows + offset}").toArray
  wordlines ++ dramBankBitlines columns

@[reducible] def matchesDramBankSubarray
    (columns : Nat) (subcircuit : SourceSubcircuit)
    (subarray : Nat) : Bool :=
  match subcircuit.instances[subarray]? with
  | some item =>
      item.name == s!"xsub{subarray}" &&
        matchesSourceInstance item (dramSubarrayName columns)
          (dramBankSubarrayConnections columns subarray)
  | none => false

@[reducible] def matchesDramBankSubarrays
    (rows columns : Nat) (subcircuit : SourceSubcircuit) : Bool :=
  (List.range (dramBankSubarrayCount rows)).all
    (matchesDramBankSubarray columns subcircuit)

@[reducible] def dramColumnName : String := "dram_column"

@[reducible] def matchesDramColumn
    (subcircuit : SourceSubcircuit) : Bool :=
  subcircuit.name == dramColumnName &&
    subcircuit.ports ==
      #["bit", "select", "selectb", "vdd", "vpre", "precharge",
        "restore", "restoreb", "sensehi", "senselo",
        "dout", "writebus"] &&
    subcircuit.devices.size == 2 &&
    subcircuit.mosfets.size == 2 &&
    subcircuit.instances.size == 7 &&
    (match subcircuit.devices[0]?, subcircuit.devices[1]?,
        subcircuit.mosfets[0]?, subcircuit.mosfets[1]?,
        subcircuit.instances[0]?, subcircuit.instances[1]?,
        subcircuit.instances[2]?, subcircuit.instances[3]?,
        subcircuit.instances[4]?, subcircuit.instances[5]?,
        subcircuit.instances[6]? with
    | some bitlineCapacitor, some referenceCapacitor,
        some precharge, some referencePrecharge,
        some truePrecharge, some complementPrecharge, some sense,
        some trueCoupling, some complementCoupling,
        some readMux, some writeMux =>
        (match bitlineCapacitor.kind, referenceCapacitor.kind with
        | .capacitor, .capacitor => true
        | _, _ => false) &&
        bitlineCapacitor.name == "cbit" &&
        bitlineCapacitor.positive == "bit" &&
        bitlineCapacitor.negative == "0" &&
        0 < bitlineCapacitor.value &&
        referenceCapacitor.name == "cref" &&
        referenceCapacitor.positive == "ref" &&
        referenceCapacitor.negative == "0" &&
        0 < referenceCapacitor.value &&
        precharge.name == "mpre" &&
        matchesSourceMosfet precharge
          "bit" "precharge" "vpre" "0" "nmod" &&
        referencePrecharge.name == "mpreref" &&
        matchesSourceMosfet referencePrecharge
          "ref" "precharge" "vpre" "0" "nmod" &&
        truePrecharge.name == "xpreq" &&
        matchesSourceInstance truePrecharge "tg"
          #["q", "vpre", "restoreb", "restore", "vdd"] &&
        complementPrecharge.name == "xpreqb" &&
        matchesSourceInstance complementPrecharge "tg"
          #["qb", "vpre", "restoreb", "restore", "vdd"] &&
        sense.name == "xsense" &&
        matchesSourceInstance sense "dram_sense_amp"
          #["q", "qb", "sensehi", "senselo"] &&
        trueCoupling.name == "xcouple" &&
        matchesSourceInstance trueCoupling "tg"
          #["bit", "q", "restore", "restoreb", "vdd"] &&
        complementCoupling.name == "xcoupleb" &&
        matchesSourceInstance complementCoupling "tg"
          #["ref", "qb", "restore", "restoreb", "vdd"] &&
        readMux.name == "xreadmux" &&
        matchesSourceInstance readMux "tg"
          #["q", "dout", "select", "selectb", "vdd"] &&
        writeMux.name == "xwritemux" &&
        matchesSourceInstance writeMux "tg"
          #["writebus", "bit", "select", "selectb", "vdd"]
    | _, _, _, _, _, _, _, _, _, _, _ => false)

@[reducible] def matchesDramBankColumn
    (rows _columns : Nat)
    (subcircuit : SourceSubcircuit) (column : Nat) : Bool :=
  let subarrays := dramBankSubarrayCount rows
  let control := dramBankBasePorts.size + rows + 2 * column
  match subcircuit.instances[subarrays + column]?,
      subcircuit.ports[control]?, subcircuit.ports[control + 1]? with
  | some item, some select, some selectBar =>
      let bitline := s!"bit{column}"
      select == s!"select{column}" &&
      selectBar == s!"selectb{column}" &&
      item.name == s!"xcolumn{column}" &&
      matchesSourceInstance item dramColumnName
        #[bitline, select, selectBar, "vdd", "vpre", "precharge",
          "restore", "restoreb", "sensehi", "senselo",
          "dout", "writebus"]
  | _, _, _ => false

@[reducible] def matchesDramBank
    (rows columns : Nat) (subcircuit : SourceSubcircuit) : Bool :=
  subcircuit.name == dramBankName rows columns &&
    subcircuit.ports.size ==
      dramBankBasePorts.size + rows + 2 * columns &&
    subcircuit.ports.toList.take dramBankBasePorts.size ==
      dramBankBasePorts.toList &&
    subcircuit.devices.isEmpty &&
    subcircuit.mosfets.isEmpty &&
    rows % dramBankSubarrayRows == 0 &&
    subcircuit.instances.size ==
      dramBankSubarrayCount rows + columns + 1 &&
    matchesDramBankSubarrays rows columns subcircuit &&
    (List.range columns).all
      (matchesDramBankColumn rows columns subcircuit) &&
    (match subcircuit.instances[
        dramBankSubarrayCount rows + columns]? with
    | some writeInput =>
        writeInput.name == "xwrite" &&
      matchesSourceInstance writeInput "tg"
          #["din", "writebus", "write", "writeb", "vdd"]
    | none => false)

/-- The source sections needed to certify the bank hierarchy. Keeping these
as a compact witness lets the kernel validate individual rows and columns
without reducing the entire source predicate in one equality. -/
structure DramBankTopologyWitness where
  senseAmplifier : SourceSubcircuit
  transmissionGate : SourceSubcircuit
  cell : SourceSubcircuit
  row : SourceSubcircuit
  subarray : SourceSubcircuit
  column : SourceSubcircuit
  bank : SourceSubcircuit
  top : SourceInstance
deriving Inhabited, Lean.ToExpr

/-- Kernel-checkable structural provenance for a concrete hierarchical bank.
Numeric model and capacitance fields are certified separately by
`toDramBankParameters`. -/
structure DramBankTopologyValid
    (source : SourceCircuit) (rows columns : Nat)
    (witness : DramBankTopologyWitness) : Prop where
  rowsPositive : 0 < rows
  columnsPositive : 0 < columns
  sourceShape :
    source.devices.isEmpty = true ∧
      source.mosfets.isEmpty = true ∧
      source.instances.size = 1 ∧
      source.subcircuits.size = 7 ∧
      source.models.size = 3
  senseAmplifierProjected :
    sourceSubcircuit? source "dram_sense_amp" =
      some witness.senseAmplifier
  transmissionGateProjected :
    sourceSubcircuit? source "tg" = some witness.transmissionGate
  cellProjected :
    sourceSubcircuit? source "dram_cell" = some witness.cell
  rowProjected :
    sourceSubcircuit? source (dramRowName columns) = some witness.row
  subarrayProjected :
    sourceSubcircuit? source (dramSubarrayName columns) =
      some witness.subarray
  columnProjected :
    sourceSubcircuit? source dramColumnName = some witness.column
  bankProjected :
    sourceSubcircuit? source (dramBankName rows columns) = some witness.bank
  topProjected : source.instances[0]? = some witness.top
  senseAmplifierValid :
    matchesDramSenseAmplifier witness.senseAmplifier = true
  transmissionGateValid :
    matchesTransmissionGate witness.transmissionGate = true
  cellValid : matchesDramCell witness.cell = true
  rowTemplateValid : matchesDramRow columns witness.row = true
  subarrayTemplateValid :
    matchesDramSubarray columns witness.subarray = true
  columnTemplateValid : matchesDramColumn witness.column = true
  bankHeaderValid :
    (witness.bank.name == dramBankName rows columns &&
      witness.bank.ports.size ==
        dramBankBasePorts.size + rows + 2 * columns &&
      witness.bank.ports.toList.take dramBankBasePorts.size ==
        dramBankBasePorts.toList &&
      witness.bank.devices.isEmpty &&
      witness.bank.mosfets.isEmpty &&
      rows % dramBankSubarrayRows == 0 &&
      witness.bank.instances.size ==
        dramBankSubarrayCount rows + columns + 1) = true
  bankSubarraysValid :
    matchesDramBankSubarrays rows columns witness.bank = true
  bankColumnsValid :
    (List.range columns).all
      (matchesDramBankColumn rows columns witness.bank) = true
  writeInputValid :
    (match witness.bank.instances[
        dramBankSubarrayCount rows + columns]? with
    | some writeInput =>
        writeInput.name == "xwrite" &&
          matchesSourceInstance writeInput "tg"
          #["din", "writebus", "write", "writeb", "vdd"]
    | none => false) = true
  topValid :
    matchesSourceInstance witness.top
      (dramBankName rows columns) witness.bank.ports = true

theorem DramBankTopologyValid.bankValid
    (valid : DramBankTopologyValid source rows columns witness) :
    matchesDramBank rows columns witness.bank = true := by
  have hrows :
      matchesDramBankSubarrays rows columns witness.bank = true :=
    valid.bankSubarraysValid
  have hcolumns :
      (List.range columns).all
          (matchesDramBankColumn rows columns witness.bank) = true :=
    valid.bankColumnsValid
  simpa only [matchesDramBank, hrows, hcolumns, Bool.and_true,
    Bool.and_eq_true] using
      And.intro valid.bankHeaderValid valid.writeInputValid

@[reducible] def dramBankTopologyMatches
    (source : SourceCircuit) (rows columns : Nat) : Bool :=
  match sourceSubcircuit? source "dram_sense_amp",
      sourceSubcircuit? source "tg",
      sourceSubcircuit? source "dram_cell",
      sourceSubcircuit? source (dramRowName columns),
      sourceSubcircuit? source (dramSubarrayName columns),
      sourceSubcircuit? source dramColumnName,
      sourceSubcircuit? source (dramBankName rows columns),
      source.instances[0]? with
  | some senseAmplifier, some transmissionGate, some cell, some row,
      some subarray, some column, some bank, some top =>
      source.devices.isEmpty &&
        source.mosfets.isEmpty &&
        source.instances.size == 1 &&
        source.subcircuits.size == 7 &&
        source.models.size == 3 &&
        matchesDramSenseAmplifier senseAmplifier &&
        matchesTransmissionGate transmissionGate &&
        matchesDramCell cell &&
        matchesDramRow columns row &&
        matchesDramSubarray columns subarray &&
        matchesDramColumn column &&
        matchesDramBank rows columns bank &&
        matchesSourceInstance top (dramBankName rows columns) bank.ports
  | _, _, _, _, _, _, _, _ => false

theorem DramBankTopologyValid.sourceValid
    (valid : DramBankTopologyValid source rows columns witness) :
    dramBankTopologyMatches source rows columns = true := by
  rcases valid.sourceShape with
    ⟨hdevices, hmosfets, hinstances, hsubcircuits, hmodels⟩
  simp only [dramBankTopologyMatches, valid.senseAmplifierProjected,
    valid.transmissionGateProjected, valid.cellProjected,
    valid.rowProjected, valid.subarrayProjected,
    valid.columnProjected,
    valid.bankProjected, valid.topProjected,
    hdevices, hmosfets, hinstances, hsubcircuits, hmodels,
    valid.senseAmplifierValid, valid.transmissionGateValid,
    valid.cellValid, valid.rowTemplateValid,
    valid.subarrayTemplateValid, valid.columnTemplateValid,
    valid.bankValid,
    valid.topValid, Bool.and_true]
  norm_num

/-- The source-level facts that connect every bank column to the reusable
differential latch. This is a structural projection: it certifies the latch,
the paired bitline/reference coupling gates, and every column instance. It
does not yet claim that the finite coupling trajectory has reached a
particular endpoint. -/
structure DramBankDifferentialSenseConnectionValid
    (source : SourceCircuit) (rows columns : Nat)
    (witness : DramBankTopologyWitness) : Prop where
  senseAmplifierProjected :
    sourceSubcircuit? source "dram_sense_amp" =
      some witness.senseAmplifier
  senseAmplifierValid :
    matchesDramSenseAmplifier witness.senseAmplifier = true
  columnProjected :
    sourceSubcircuit? source dramColumnName = some witness.column
  columnValid : matchesDramColumn witness.column = true
  bankColumnsValid :
    (List.range columns).all
      (matchesDramBankColumn rows columns witness.bank) = true

theorem DramBankTopologyValid.differentialSenseConnectionValid
    (valid : DramBankTopologyValid source rows columns witness) :
    DramBankDifferentialSenseConnectionValid
      source rows columns witness :=
  { senseAmplifierProjected := valid.senseAmplifierProjected
    senseAmplifierValid := valid.senseAmplifierValid
    columnProjected := valid.columnProjected
    columnValid := valid.columnTemplateValid
    bankColumnsValid := valid.bankColumnsValid }

/-- Exact source parameters retained before selecting the real-valued
interpretation used by physical semantics. -/
structure DramBankSourceParameters (columns : Nat) where
  accessThreshold : Rat
  accessBeta : Rat
  storageCapacitance : Rat
  bitlineCapacitances : Array Rat
  referenceBitlineCapacitances : Array Rat
  pThreshold : Rat
  pBeta : Rat
  senseNThreshold : Rat
  senseNBeta : Rat
  sensePThreshold : Rat
  sensePBeta : Rat
  senseTrueCapacitance : Rat
  senseComplementCapacitance : Rat
deriving Repr, Inhabited, Lean.ToExpr

noncomputable def DramBankSourceParameters.toCoreProfile
    (parameters : DramBankSourceParameters columns)
    (rows : Nat) : DramBankCoreProfile rows columns :=
  { cells := fun _row column =>
      { threshold := parameters.accessThreshold
        beta := parameters.accessBeta
        storageCapacitance := parameters.storageCapacitance
        bitlineCapacitance :=
          parameters.bitlineCapacitances[column.val]?.getD 0 }
    pThreshold := parameters.pThreshold
    pBeta := parameters.pBeta
    sensePThreshold := parameters.sensePThreshold
    sensePBeta := parameters.sensePBeta }

/-- The exact latch instance projected from the shared source models and the
two capacitors inside `dram_sense_amp`. -/
noncomputable def DramBankSourceParameters.toDifferentialSenseInstance
    (parameters : DramBankSourceParameters columns) :
    DramDifferentialSenseInstance :=
  { nThreshold := parameters.senseNThreshold
    pThreshold := parameters.sensePThreshold
    nBeta := parameters.senseNBeta
    pBeta := parameters.sensePBeta
    trueCapacitance := parameters.senseTrueCapacitance
    complementCapacitance := parameters.senseComplementCapacitance }

/-- The paired transmission-gate/capacitor coupling instance for one
source-projected bank column. -/
noncomputable def DramBankSourceParameters.toSenseCouplingInstance
    (parameters : DramBankSourceParameters columns)
    (column : Fin columns) : DramSenseCouplingInstance :=
  { nThreshold := parameters.accessThreshold
    nBeta := parameters.accessBeta
    pThreshold := parameters.pThreshold
    pBeta := parameters.pBeta
    bitlineCapacitance :=
      parameters.bitlineCapacitances[column.val]?.getD 0
    referenceCapacitance :=
      parameters.referenceBitlineCapacitances[column.val]?.getD 0
    trueCapacitance := parameters.senseTrueCapacitance
    complementCapacitance :=
      parameters.senseComplementCapacitance }

/-- Kernel-friendly exact parameter projection. Structural topology validation
is deliberately separate so a large hierarchy can be certified in chunks;
this function is the source of every numeric field used by semantics. -/
def SourceCircuit.toDramBankParameters
    (source : SourceCircuit) (rows columns : Nat) :
    Except String (DramBankSourceParameters columns) := do
  if rows == 0 || columns == 0 then
    throw "DRAM bank dimensions must both be positive"
  let cell ←
    optionToExcept (sourceSubcircuit? source "dram_cell")
      "missing `dram_cell` subcircuit"
  let column ←
    optionToExcept (sourceSubcircuit? source dramColumnName)
      "missing `dram_column` subcircuit"
  let sense ←
    optionToExcept (sourceSubcircuit? source "dram_sense_amp")
      "missing `dram_sense_amp` subcircuit"
  let nmod ←
    optionToExcept (sourceModel? source "nmod") "missing `nmod` model"
  let pmod ←
    optionToExcept (sourceModel? source "pmod") "missing `pmod` model"
  let psense ←
    optionToExcept (sourceModel? source "psense") "missing `psense` model"
  if cell.devices.size == 1 &&
      (match cell.devices[0]? with
      | some capacitor =>
          (match capacitor.kind with
          | .capacitor => true
          | _ => false) &&
          0 < capacitor.value
      | none => false) &&
      column.devices.size == 2 &&
      (match column.devices[0]?, column.devices[1]? with
      | some bitlineCapacitor, some referenceCapacitor =>
          (match bitlineCapacitor.kind, referenceCapacitor.kind with
          | .capacitor, .capacitor => true
          | _, _ => false) &&
          0 < bitlineCapacitor.value &&
          0 < referenceCapacitor.value
      | _, _ => false) &&
      sense.devices.size == 2 &&
      (match sense.devices[0]?, sense.devices[1]? with
      | some trueCapacitor, some complementCapacitor =>
          (match trueCapacitor.kind, complementCapacitor.kind with
          | .capacitor, .capacitor => true
          | _, _ => false) &&
          0 < trueCapacitor.value &&
          0 < complementCapacitor.value
      | _, _ => false) &&
      validSourceModel nmod "nmod" .nmos &&
      validSourceModel pmod "pmod" .pmos &&
      validSourceModel psense "psense" .pmos then
    pure {
      accessThreshold := nmod.threshold
      accessBeta := nmod.transconductance
      storageCapacitance := (cell.devices[0]!).value
      bitlineCapacitances :=
        Array.replicate columns (column.devices[0]!).value
      referenceBitlineCapacitances :=
        Array.replicate columns (column.devices[1]!).value
      pThreshold := -pmod.threshold
      pBeta := pmod.transconductance
      senseNThreshold := nmod.threshold
      senseNBeta := nmod.transconductance
      sensePThreshold := -psense.threshold
      sensePBeta := psense.transconductance
      senseTrueCapacitance := (sense.devices[0]!).value
      senseComplementCapacitance := (sense.devices[1]!).value }
  else
    throw
      s!"source parameters are outside the supported {rows}x{columns} \
      DRAM endpoint-contract profile"

/-- A source-derived bank artifact. No source name or numeric parameter
survives as a semantic lookup: all values have already been projected into
the typed profile. -/
structure CheckedDramBank (rows columns : Nat) where
  parameters : DramBankSourceParameters columns
deriving Inhabited, Lean.ToExpr

noncomputable def CheckedDramBank.profile
    (bank : CheckedDramBank rows columns) :
    DramBankCoreProfile rows columns :=
  bank.parameters.toCoreProfile rows

def SourceCircuit.toDramBank
    (source : SourceCircuit) (rows columns : Nat) :
    Except String (CheckedDramBank rows columns) := do
  if rows == 0 || columns == 0 then
    throw "DRAM bank dimensions must both be positive"
  let parameters ←
    LeanModels.Spice.SourceCircuit.toDramBankParameters
      source rows columns
  if dramBankTopologyMatches source rows columns then
    pure ⟨parameters⟩
  else
    throw
      s!"source does not match the checked hierarchical {rows}x{columns} \
      DRAM endpoint-contract prototype"

theorem SourceCircuit.toDramBank_eq_ok
    (parameters : DramBankSourceParameters columns)
    (witness : DramBankTopologyWitness)
    (hparameters :
      LeanModels.Spice.SourceCircuit.toDramBankParameters
        source rows columns = .ok parameters)
    (htopology :
      DramBankTopologyValid source rows columns witness) :
    LeanModels.Spice.SourceCircuit.toDramBank source rows columns =
      .ok (⟨parameters⟩ : CheckedDramBank rows columns) := by
  have hrows : rows ≠ 0 := Nat.ne_of_gt htopology.rowsPositive
  have hcolumns : columns ≠ 0 :=
    Nat.ne_of_gt htopology.columnsPositive
  simp [LeanModels.Spice.SourceCircuit.toDramBank, hparameters,
    htopology.sourceValid, hrows, hcolumns]

@[reducible] def checkedDramBankOf
  (source : SourceCircuit) (rows columns : Nat) :
    CheckedDramBank rows columns :=
  (LeanModels.Spice.SourceCircuit.toDramBank
      source rows columns).toOption.getD default

@[reducible] def dramBankSourceMatches
    (source : SourceCircuit) (rows columns : Nat) : Bool :=
  (LeanModels.Spice.SourceCircuit.toDramBank
      source rows columns).isOk

@[reducible] def dramBank256x32SourceMatches
    (source : SourceCircuit) : Bool :=
  dramBankSourceMatches source dramBank256Rows dramBank256Columns

end LeanModels.Spice

namespace LeanModels.Circuit.Spice

def SourceCircuit.toDramBankParameters
    (source : SourceCircuit) (rows columns : Nat) :
    Except String (LeanModels.Spice.DramBankSourceParameters columns) :=
  LeanModels.Spice.SourceCircuit.toDramBankParameters source rows columns

def SourceCircuit.toDramBank
    (source : SourceCircuit) (rows columns : Nat) :
    Except String (LeanModels.Spice.CheckedDramBank rows columns) :=
  LeanModels.Spice.SourceCircuit.toDramBank source rows columns

end LeanModels.Circuit.Spice

/-!
`load_dram_bank` embeds the parsed hierarchical source, its source-derived
rational parameters, and a typed topology witness. It emits separate
kernel-checked parameter and topology theorems, then derives the complete
`SourceCircuit.toDramBank` projection. The row, subarray, and column hierarchy
keeps each certificate bounded instead of reducing a flattened 8,192-cell
term.
-/

open Lean Elab Command in
elab "load_dram_bank " name:ident " from " path:str
    " rows " rowsSyntax:num " columns " columnsSyntax:num : command => do
  let rows := rowsSyntax.getNat
  let columns := columnsSyntax.getNat
  let pathString := path.getString
  let contents ←
    match ← (IO.FS.readFile ⟨pathString⟩).toBaseIO with
    | .ok contents => pure contents
    | .error error =>
        throwErrorAt path
          "load_dram_bank: cannot read '{pathString}': {toString error}"
  let source ←
    match LeanModels.Circuit.Spice.parse contents with
    | .ok source => pure source
    | .error error =>
        throwErrorAt path
          "load_dram_bank: {error.describe}"
  let checked ←
    match LeanModels.Spice.SourceCircuit.toDramBank
        source rows columns with
    | .ok checked => pure checked
    | .error error => throwErrorAt path "load_dram_bank: {error}"
  let topology : LeanModels.Spice.DramBankTopologyWitness ←
    match LeanModels.Spice.sourceSubcircuit? source "dram_sense_amp",
        LeanModels.Spice.sourceSubcircuit? source "tg",
        LeanModels.Spice.sourceSubcircuit? source "dram_cell",
        LeanModels.Spice.sourceSubcircuit? source
          (LeanModels.Spice.dramRowName columns),
        LeanModels.Spice.sourceSubcircuit? source
          (LeanModels.Spice.dramSubarrayName columns),
        LeanModels.Spice.sourceSubcircuit? source
          LeanModels.Spice.dramColumnName,
        LeanModels.Spice.sourceSubcircuit? source
          (LeanModels.Spice.dramBankName rows columns),
        source.instances[0]? with
    | some senseAmplifier, some transmissionGate, some cell, some row,
        some subarray, some column, some bank, some top =>
        pure {
          senseAmplifier := senseAmplifier
          transmissionGate := transmissionGate
          cell := cell
          row := row
          subarray := subarray
          column := column
          bank := bank
          top := top }
    | _, _, _, _, _, _, _, _ =>
        throwErrorAt path
          "load_dram_bank: internal topology witness extraction failed"
  let declarationName := (← getCurrNamespace) ++ name.getId
  let companionName (suffix : String) : Name :=
    .str declarationName.getPrefix (declarationName.getString! ++ suffix)
  let checkedName := companionName "_checked"
  let topologyName := companionName "_topology"
  if (← getEnv).contains declarationName then
    throwErrorAt name
      "load_dram_bank: '{declarationName}' has already been declared"
  liftCoreM do
    addAndCompile <| .defnDecl {
      name := declarationName
      levelParams := []
      type := Lean.mkConst ``LeanModels.Circuit.Spice.SourceCircuit
      value := Lean.toExpr source
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst declarationName
    let checkedValue := Lean.toExpr checked
    let checkedType :=
      Lean.mkApp2
        (Lean.mkConst ``LeanModels.Spice.CheckedDramBank)
        (Lean.mkNatLit rows) (Lean.mkNatLit columns)
    addAndCompile <| .defnDecl {
      name := checkedName
      levelParams := []
      type := checkedType
      value := checkedValue
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst checkedName
    let topologyValue := Lean.toExpr topology
    let topologyType :=
      Lean.mkConst ``LeanModels.Spice.DramBankTopologyWitness
    addAndCompile <| .defnDecl {
      name := topologyName
      levelParams := []
      type := topologyType
      value := topologyValue
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst topologyName
  modifyEnv fun environment =>
    LeanModels.Circuit.circuitSourceTables.modifyState environment fun tables =>
      tables.insert declarationName source
  modifyEnv fun environment =>
    LeanModels.Circuit.circuitProvenanceTables.modifyState environment
      fun tables =>
        tables.insert declarationName ⟨pathString, hash contents⟩
  let sourceId := mkIdent declarationName
  let checkedId := mkIdent checkedName
  let topologyId := mkIdent topologyName
  let projectionId :=
    mkIdent
      (.mkSimple
        (declarationName.getString! ++ "_parameter_projection"))
  let topologyProjectionId :=
    mkIdent
      (.mkSimple
        (declarationName.getString! ++ "_topology_projection"))
  let completeProjectionId :=
    mkIdent (.mkSimple (declarationName.getString! ++ "_projection"))
  let rowsTerm := quote rows
  let columnsTerm := quote columns
  elabCommand (← `(set_option maxRecDepth 100000 in
    set_option maxHeartbeats 0 in
    theorem $projectionId :
        LeanModels.Circuit.Spice.SourceCircuit.toDramBankParameters
            $sourceId $rowsTerm $columnsTerm =
          .ok ($checkedId).parameters := by
      circuit_reduce))
  elabCommand (← `(set_option maxRecDepth 100000 in
    set_option maxHeartbeats 0 in
    theorem $topologyProjectionId :
        LeanModels.Spice.DramBankTopologyValid
          $sourceId $rowsTerm $columnsTerm $topologyId := by
      refine {
        rowsPositive := by norm_num
        columnsPositive := by norm_num
        sourceShape := ⟨rfl, rfl, rfl, rfl, rfl⟩
        senseAmplifierProjected := by circuit_reduce
        transmissionGateProjected := by circuit_reduce
        cellProjected := by circuit_reduce
        rowProjected := by circuit_reduce
        subarrayProjected := by circuit_reduce
        columnProjected := by circuit_reduce
        bankProjected := by circuit_reduce
        topProjected := by circuit_reduce
        senseAmplifierValid := by circuit_reduce
        transmissionGateValid := by circuit_reduce
        cellValid := by circuit_reduce
        rowTemplateValid := by circuit_reduce
        subarrayTemplateValid := by circuit_reduce
        columnTemplateValid := by circuit_reduce
        bankHeaderValid := by circuit_reduce
        bankSubarraysValid := by circuit_reduce
        bankColumnsValid := by circuit_reduce
        writeInputValid := by circuit_reduce
        topValid := by circuit_reduce }
      ))
  elabCommand (← `(theorem $completeProjectionId :
      LeanModels.Circuit.Spice.SourceCircuit.toDramBank
          $sourceId $rowsTerm $columnsTerm =
        .ok $checkedId := by
    exact LeanModels.Spice.SourceCircuit.toDramBank_eq_ok
      ($checkedId).parameters $topologyId
      $projectionId $topologyProjectionId))
  liftTermElabM do
    Term.addTermInfo' name (Lean.mkConst declarationName) (isBinder := true)
