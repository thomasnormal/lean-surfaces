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

#print axioms half_adder_correct
