import Examples.spice.and_gate.proof

open LeanModels.Spice

load_netlist andGateDeck from "Examples/spice/and_gate/and_gate.json"

#guard andGateDeck.hasUnsupported == false
#guard match flatten andGateDeck with
  | .error (.unsupported "M" _) => true
  | _ => false

/-- For all four input vectors, every ideal-switch state of the extracted
CMOS network has `out = a && b`, and at least one such state exists. -/
theorem cmos_and_correct :
    BinaryGateContract andGateDeck "a" "b" "out" (· && ·) := by proofs

#print axioms cmos_and_correct
