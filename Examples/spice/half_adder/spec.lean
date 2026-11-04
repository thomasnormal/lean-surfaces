import Examples.spice.half_adder.proof
import LeanModels.Python.Surface

open LeanModels.Circuit LeanModels.Spice

load_circuit halfAdderDeck from "Examples/spice/half_adder/half_adder.cir"

#guard sharedToMos1Circuit halfAdderDeck matches .ok _

abbrev halfAdderMos1 := Examples.spice.half_adder.proof.halfAdderMos1

/-- The extracted transistor hierarchy proved directly from its exact ngspice
MOS Level-1 equations and KCL, within the 0--5 V operating envelope. -/
theorem half_adder_mos1_correct :
    Mos1HalfAdderContract halfAdderMos1
      (mos_node! halfAdderMos1 "a") (mos_node! halfAdderMos1 "b")
      (mos_node! halfAdderMos1 "sum")
      (mos_node! halfAdderMos1 "carry") := by proofs

theorem half_adder_mos1_observation_exists (left right : Bool) :
    Mos1HalfAdderObservation halfAdderMos1
      (mos_node! halfAdderMos1 "a") (mos_node! halfAdderMos1 "b")
      (mos_node! halfAdderMos1 "sum")
      (mos_node! halfAdderMos1 "carry")
      left right (Bool.xor left right) (Bool.and left right) := by proofs

#print axioms half_adder_mos1_correct
#print axioms half_adder_mos1_observation_exists
