import Examples.spice.chain.proof

open LeanModels.Circuit
open Examples.spice.chain.proof

load_circuit chainSpecDeck from "Examples/spice/chain/chain.cir"

#circuit_check chainSpecDeck dc shows "out3" = (2 / 3 : Rat) ^ 3 * 5

theorem attn_is_extracted :
    attn.name = "attn" ∧ attn.portNames = #["a", "b"] := by proofs

theorem section_contract :
    HasExactContract attn.PortBehavior attnContract := by proofs

theorem two_section_contract :
    HasExactContract
      (CascadeRelation attn.PortBehavior attn.PortBehavior)
      (cascade attnContract attnContract) := by proofs

theorem chain_contract (sections : Nat) (input output inputCurrent : Rat) :
    LoadedChain sections input output inputCurrent ↔
      output = (2 / 3 : Rat) ^ sections * input ∧ inputCurrent = input / 3000 := by proofs

theorem chain_attenuates (sections : Nat) (output inputCurrent : Rat)
    (h : LoadedChain sections 5 output inputCurrent) :
    output = (2 / 3 : Rat) ^ sections * 5 := by proofs

theorem approx_attenuator_contract :
    HasErrorBoundedContract ApproxAttenuatorBehavior
      ApproxAttenuatorContract := by proofs

theorem two_approx_attenuators_contract :
    HasErrorBoundedContract
      (SerialScalarRelation ApproxAttenuatorBehavior
        ApproxAttenuatorBehavior)
      (composeErrorContracts ApproxAttenuatorContract
        ApproxAttenuatorContract) := by proofs

theorem two_approx_attenuators_error :
    (composeErrorContracts ApproxAttenuatorContract
      ApproxAttenuatorContract).error = (1 / 60 : ℝ) := by proofs

#print axioms section_contract
#print axioms two_section_contract
#print axioms chain_contract
#print axioms chain_attenuates
#print axioms two_approx_attenuators_contract
#print axioms two_approx_attenuators_error
