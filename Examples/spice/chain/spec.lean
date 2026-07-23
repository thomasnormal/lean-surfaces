import Examples.spice.chain.proof

open LeanModels.Spice
open Examples.spice.chain.proof

/- This instance is deliberately beyond the three sections in `chain.cir`:
it checks that the executable AST family, hierarchy flattener, and exact MNA
solver agree on a newly generated composite. -/
#spice_check chain 5 shows "out5" = (2 / 3 : Rat) ^ 5 * 5

theorem attn_is_extracted : chainDeck.subckts[0]? = some (.definition attn) := by proofs

theorem section_contract : HasContract attn attnContract := by proofs

theorem chain_contract (sections : Nat) (input output inputCurrent : Rat) :
    LoadedChain sections input output inputCurrent ↔
      output = (2 / 3 : Rat) ^ sections * input ∧ inputCurrent = input / 3000 := by proofs

theorem chain_attenuates (sections : Nat) (output inputCurrent : Rat)
    (h : LoadedChain sections 5 output inputCurrent) :
    output = (2 / 3 : Rat) ^ sections * 5 := by proofs

#print axioms section_contract
#print axioms chain_contract
#print axioms chain_attenuates
