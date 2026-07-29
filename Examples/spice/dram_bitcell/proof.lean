import LeanModels.Spice.DramBitcell
import LeanModels.Circuit.Surface

namespace Examples.spice.dram_bitcell.proof

open LeanModels.Circuit LeanModels.Spice

load_circuit dramBitcell from
  "Examples/spice/dram_bitcell/dram_bitcell.cir"

theorem dram_bitcell_topology :
    dramBitcell.toDramReadNominal = .ok
      { storageNode := ⟨0⟩
        wordlineNode := ⟨3⟩
        bitlineNode := ⟨2⟩
        threshold := 1
        beta := 1 / 10000
        storageCapacitance := 3 / 100000000000000
        bitlineCapacitance := 3 / 10000000000000 } := by
  rfl

noncomputable def nominalRead : DramReadParameters :=
  { supply := 5
    storageCapacitance := 30
    bitlineCapacitance := 300
    precharge := 5 / 2 }

def DramBitcellReadSpecification
    (stored : Bool) (observation : DramReadObservation) : Prop :=
  observation.sensed = stored ∧
    observation.restoredVoltage = dramStoredVoltage nominalRead stored

theorem nominalRead_admissible : DramReadAdmissible nominalRead := by
  norm_num [DramReadAdmissible, nominalRead]

theorem dram_bitcell_equation_manifest (stored : Bool) :
    EquationManifest
      (DramReadProgram nominalRead stored)
      ["ideal sense discriminator", "ideal restore endpoint"] :=
  dramReadEquationManifest

theorem dram_bitcell_read_realizable (stored : Bool) :
    ∃ observation, DramReadBehavior nominalRead stored observation :=
  dram_read_realizable nominalRead_admissible stored

theorem dram_bitcell_read_correct
    {stored : Bool} {observation : DramReadObservation}
    (hread : DramReadBehavior nominalRead stored observation) :
    observation.sensed = stored ∧
      observation.restoredVoltage = dramStoredVoltage nominalRead stored :=
  dram_read_correct nominalRead_admissible hread

theorem dram_bitcell_sense_margin (stored : Bool) :
    |dramSharedVoltage nominalRead stored - nominalRead.precharge| =
      5 / 22 := by
  convert dram_read_margin nominalRead_admissible stored using 1 <;>
    norm_num [nominalRead]

theorem dram_bank_read_all_widths
    {width : Nat} {before : DramBankState width} {address : Fin width}
    {output : Bool} {after : DramBankState width}
    (hread :
      DramBankReadContract nominalRead before address output after) :
    output = before.bits address ∧ after = before :=
  dram_bank_read_refines nominalRead_admissible hread

theorem dram_bank_write_all_widths
    {width : Nat} {before after : DramBankState width}
    {address : Fin width} {input : Bool}
    (hwrite : DramBankWriteContract before address input after) :
    after.bits address = input ∧
      ∀ other, other ≠ address →
        after.bits other = before.bits other :=
  dram_bank_write_refines hwrite

#equation_guard DramReadProgram forbids [DramBitcellReadSpecification]

#equation_report dram_bitcell_equation_manifest

end Examples.spice.dram_bitcell.proof
