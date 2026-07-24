import Examples.spice.half_adder.proof

open LeanModels.Spice

load_mos1 halfAdderDeck from "Examples/spice/half_adder/half_adder.json"

#guard halfAdderDeck.hasUnsupported == false
#guard halfAdderDeck.toMos1 matches .ok _
#guard match flattenSwitch halfAdderDeck with
  | .ok flat => flat.cards.size == 25
  | .error _ => false

/-- Every ideal-switch state of the extracted transistor hierarchy computes
the one-bit sum and carry, and such a state exists for every input vector. -/
theorem half_adder_correct :
    HalfAdderContract halfAdderDeck "a" "b" "sum" "carry" := by proofs

theorem half_adder_interface
    {left right sum carry : Bool} :
    HalfAdderObservation halfAdderDeck "a" "b" "sum" "carry"
        left right sum carry ↔
      HalfAdderBehavior left right sum carry := by proofs

abbrev halfAdderMos1 := Examples.spice.half_adder.proof.halfAdderMos1

/-- The extracted transistor hierarchy proved directly from its exact ngspice
MOS Level-1 equations and KCL, within the 0--5 V operating envelope. -/
theorem half_adder_mos1_correct :
    Mos1HalfAdderContract halfAdderMos1
      (node! halfAdderMos1 "a") (node! halfAdderMos1 "b")
      (node! halfAdderMos1 "sum") (node! halfAdderMos1 "carry") := by proofs

#print axioms half_adder_correct
#print axioms half_adder_interface
#print axioms half_adder_mos1_correct
