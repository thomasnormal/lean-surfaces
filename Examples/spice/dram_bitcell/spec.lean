import LeanModels.Python.Surface
import Examples.spice.dram_bitcell.proof

open LeanModels.Spice
open Examples.spice.dram_bitcell.proof

theorem dram_bitcell_read_realizable (stored : Bool) :
    ∃ observation, DramReadBehavior nominalRead stored observation := by proofs

theorem dram_bitcell_read_correct
    {stored : Bool} {observation : DramReadObservation}
    (hread : DramReadBehavior nominalRead stored observation) :
    observation.sensed = stored ∧
      observation.restoredVoltage = dramStoredVoltage nominalRead stored := by proofs

theorem dram_bitcell_sense_margin (stored : Bool) :
    |dramSharedVoltage nominalRead stored - nominalRead.precharge| =
      5 / 22 := by proofs

theorem dram_bank_read_all_widths
    {width : Nat} {before : DramBankState width} {address : Fin width}
    {output : Bool} {after : DramBankState width}
    (hread :
      DramBankReadBehavior nominalRead before address output after) :
    output = before.bits address ∧ after = before := by proofs

theorem dram_bank_write_all_widths
    {width : Nat} {before after : DramBankState width}
    {address : Fin width} {input : Bool}
    (hwrite : DramBankWriteBehavior before address input after) :
    after.bits address = input ∧
      ∀ other, other ≠ address →
        after.bits other = before.bits other := by proofs

#print axioms dram_bitcell_read_realizable
#print axioms dram_bitcell_read_correct
#print axioms dram_bitcell_sense_margin
#print axioms dram_bank_read_all_widths
#print axioms dram_bank_write_all_widths
