import Examples.spice.and_gate.proof
import LeanModels.Python.Surface

open LeanModels.Circuit LeanModels.Spice

load_circuit andGateDeck from "Examples/spice/and_gate/and_gate.cir"

#guard sharedToMos1Circuit andGateDeck matches .ok _

abbrev andGateMos1 := Examples.spice.and_gate.proof.andGateMos1

/-- The same extracted transistor deck proved directly against its exact
ngspice MOS Level-1 equations and KCL, within the 0–5 V operating envelope. -/
theorem cmos_and_mos1_correct :
    Mos1BinaryGateContract andGateMos1
      (mos_node! andGateMos1 "a") (mos_node! andGateMos1 "b")
      (mos_node! andGateMos1 "out") (· && ·) := by proofs

#print axioms cmos_and_mos1_correct
