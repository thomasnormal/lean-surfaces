import Examples.spice.and_gate.proof
import LeanModels.Python.Surface

open LeanModels.Circuit LeanModels.Spice

-- Loudness guard (family-architecture.md §autoImplicit ruling, 2026-08-24):
-- without this a mistyped or unopened name is silently auto-bound as an
-- implicit variable rather than reported. This file is monomorphic --
-- no `Type`/`Sort` binders, no generic type variables -- so the flip is
-- inert here, and it is file-local: importers are unaffected.
set_option autoImplicit false

load_circuit andGateDeck from "Examples/spice/and_gate/and_gate.cir"

#guard sharedToMos1Circuit andGateDeck matches .ok _

abbrev andGateMos1 := Examples.spice.and_gate.proof.andGateMos1

/-- The same extracted transistor deck proved directly against its exact
ngspice MOS Level-1 equations and KCL, within the 0–5 V operating envelope. -/
theorem cmos_and_mos1_correct :
    Mos1BinaryGateContract andGateMos1
      (mos_node! andGateMos1 "a") (mos_node! andGateMos1 "b")
      (mos_node! andGateMos1 "out") (· && ·) := by proofs

/-- The universal contract is paired with an explicit non-vacuity result:
every input vector really has a state satisfying the MOS1 equations, the
supply envelope and the drivers. Without it the contract above would hold
just as well of a deck no state satisfies. -/
theorem and_gate_mos1_observation_exists (left right : Bool) :
    Mos1BinaryGateObservation andGateMos1
      (mos_node! andGateMos1 "a") (mos_node! andGateMos1 "b")
      (mos_node! andGateMos1 "out")
      left right (Bool.and left right) := by proofs

#print axioms cmos_and_mos1_correct
#print axioms and_gate_mos1_observation_exists
