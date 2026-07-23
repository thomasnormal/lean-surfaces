import Examples.spice.half_adder.proof

open LeanModels.Spice

load_netlist halfAdderDeck from "Examples/spice/half_adder/half_adder.json"

#guard halfAdderDeck.hasUnsupported == false
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

/-- The extracted transistor hierarchy proved directly from its exact ngspice
MOS Level-1 equations and KCL, within the 0--5 V operating envelope. -/
theorem half_adder_mos1_correct :
    Mos1HalfAdderContract halfAdderDeck "a" "b" "sum" "carry" := by proofs

#print axioms half_adder_correct
#print axioms half_adder_interface
#print axioms half_adder_mos1_correct
