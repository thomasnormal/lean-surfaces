import LeanModels.Circuit
import LeanModels.Circuit.DCRunner
import LeanModels.Spice.Mos1Resolved
import LeanModels.Spice.Mos1
import LeanModels.Spice.RippleNetlist
import LeanModels.Spice.LoadedRC

/-!
# Shared-core SPICE smoke tests

These tests ingest the literal `.cir` sources through the same Lean frontend
used by specifications. No JSON envelope or legacy netlist semantics exists
on this path.
-/

namespace LeanModels.Spice

open LeanModels.Circuit

load_circuit dividerFixture from "Examples/spice/divider/divider.cir"
load_circuit chainFixture from "Examples/spice/chain/chain.cir"
load_circuit r2rFixture from "Examples/spice/r2r/r2r.cir"
load_circuit robustDividerFixture from
  "Examples/spice/robust_divider/robust_divider.cir"
load_circuit loadedRCFixture from "Examples/spice/loaded_rc/loaded_rc.cir"
load_circuit andGateFixture from "Examples/spice/and_gate/and_gate.cir"
load_circuit halfAdderFixture from
  "Examples/spice/half_adder/half_adder.cir"
load_circuit_source rippleAdderFixture from
  "Examples/spice/ripple_adder/ripple_adder.cir"

#guard dividerFixture_solution.voltages == #[5, 0, 10 / 3]
#guard chainFixture_solution.assignment.voltage
    (node! chainFixture "out1").id == 10 / 3
#guard chainFixture_solution.assignment.voltage
    (node! chainFixture "out2").id == 20 / 9
#guard chainFixture_solution.assignment.voltage
    (node! chainFixture "out3").id == 40 / 27
#guard r2rFixture_solution.assignment.voltage
    (node! r2rFixture "out").id == 25 / 8

#guard robustDividerFixture.deviceNames == #["v1", "r1", "r2"]
#guard loadedRCFixture.deviceNames ==
  #["vstep", "rdrive", "rload", "cload"]
#guard andGateFixture_mos1.devices.size == 6
#guard halfAdderFixture_mos1.devices.size == 20
#guard sharedToMos1Circuit andGateFixture matches .ok _
#guard sharedToMos1Circuit halfAdderFixture matches .ok _

private noncomputable def testNmos : Mos1Params :=
  { polarity := .nmos, threshold := 1, beta := 1 / 10000, lambda := 0 }

example : mos1TerminalCurrent testNmos 5 2 0 = 3 / 5000 := by
  norm_num [testNmos, mos1TerminalCurrent, mos1ForwardCurrent]

example : mos1TerminalCurrent testNmos 5 0 2 = -(3 / 5000) := by
  norm_num [testNmos, mos1TerminalCurrent, mos1ForwardCurrent]

example :
    mos1TerminalCurrent testNmos 5 0 2 =
      -mos1TerminalCurrent testNmos 5 2 0 :=
  mos1TerminalCurrent_swap testNmos 5 2 0

#guard (expandHalfAdderCalls rippleAdderFixture).toOption.map List.length ==
  some 150
#guard embeddedHalfAdderShape? rippleAdderFixture ==
  standaloneHalfAdderShape? halfAdderFixture_source

#guard
  (match LeanModels.Circuit.Spice.parseAndElaborate
      "missing model\nM1 out in 0 0 absent\n.end" with
  | .error _ => true
  | .ok circuit =>
      sharedToMos1Circuit circuit matches .error (.missingModel _))

#guard
  (match LeanModels.Circuit.Spice.parseAndElaborate
      "invalid model\n.model nmod nmos (level=2 vto=1 kp=1u)\n.end" with
  | .error _ => true
  | .ok circuit =>
      sharedToMos1Circuit circuit matches .error (.invalidModel _))

#print axioms LeanModels.Circuit.solveDC_satisfies
#print axioms Mos1Satisfies.kclAt
#print axioms Mos1Satisfies.toBidirectional
#print axioms Mos1ComponentSatisfies.toBidirectional
#print axioms Mos1WithinSupply.boundsAt

end LeanModels.Spice
