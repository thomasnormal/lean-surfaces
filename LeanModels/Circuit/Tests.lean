import LeanModels.Circuit.Surface
import LeanModels.Circuit.Discipline

namespace LeanModels.Circuit.Tests

open LeanModels.Circuit

load_circuit directDivider from
  "Examples/spice/typed_divider/typed_divider.cir"
load_circuit assuranceMismatchCircuit from
  "Examples/spice/loaded_rc/loaded_rc.cir"
load_circuit sharedMosGate from
  "Examples/spice/and_gate/and_gate.cir"

#guard directDivider.nodeNames == #["in", "0", "out"]
#guard directDivider.deviceNames == #["v1", "r1", "r2"]
#guard directDivider_solution.voltages == #[5, 0, 10 / 3]
#guard directDivider_solution.currents == #[-1 / 600, 1 / 600, 1 / 600]
#guard decide (DCSatisfies directDivider_dc directDivider_solution.assignment)
#guard sharedMosGate.devices.size == 6
#guard sharedMosGate.models.size == 2
#guard sharedMosGate_mos1.devices.size == 6
#guard LeanModels.Spice.sharedToMos1Circuit sharedMosGate matches .ok _

theorem directDivider_trivial_assurance :
    AssuranceCase directDivider (NominalDCBehavior directDivider)
      (fun _world => True)
      (fun _world _assignment _internal => True)
      (fun _world _assignment _internal => True) := by
  constructor
  · intro _world _assignment _internal _hallowed _hbehavior
    exact True.intro
  · intro _world _hallowed
    exact ⟨directDivider_solution.assignment, (),
      directDivider_solution_satisfies⟩
  · intro _world _assignment _internal _hallowed _hbehavior
    exact True.intro

/--
error: #assurance_report: `LeanModels.Circuit.Tests.directDivider_trivial_assurance` is attached to a different elaborated circuit
-/
#guard_msgs in
#assurance_report assuranceMismatchCircuit using
  directDivider_trivial_assurance []

#guard Spice.parseValue "1k" == some 1000
#guard Spice.parseValue "2.2meg" == some 2200000
#guard Spice.parseValue "470u" == some (47 / 100000)
#guard Spice.parseValue "1.5" == some (3 / 2)
#guard Spice.parseValue "1e3" == some 1000
#guard Spice.parseValue "2.5e-3" == some (1 / 400)
#guard Spice.parseValue "1f" == some (1 / 1000000000000000)

private def malformedGround : DCCircuit :=
  { title := "malformed ground"
    nodeNames := #["0"]
    deviceNames := #[]
    ground := ⟨99⟩
    devices := #[] }

private def malformedEndpoint : DCCircuit :=
  { title := "malformed endpoint"
    nodeNames := #["0"]
    deviceNames := #["r1"]
    ground := ⟨0⟩
    devices := #[.resistor ⟨0⟩ ⟨5⟩ ⟨6⟩ 1] }

#guard !dcSatisfiesBool malformedGround ⟨#[0], #[]⟩
#guard !dcSatisfiesBool malformedEndpoint ⟨#[0], #[0]⟩

#guard
  Spice.parseAndElaborateDC
    "missing ground\nV1 in ref DC 5\nR1 in out 1k\n.end"
      matches .error _

#guard
  Spice.parseAndElaborateDC
    "zero resistor\nV1 in 0 DC 5\nR1 in 0 0\n.end"
      matches .error _

#guard
  Spice.parseAndElaborateDC
    "duplicate\nV1 in 0 DC 5\nV1 out 0 DC 2\n.end"
      matches .error _

#guard
  Spice.parseAndElaborateDC
    "inductor\nL1 in 0 1u\nR1 in 0 1\n.end"
      matches .ok _

#guard
  Spice.parseAndElaborate
    "invalid inductor\nL1 in 0 0\n.end"
      matches .error _

#guard
  (match Spice.parseAndElaborateDC
      "loaded RC\nV1 in 0 DC 5\nR1 in out 1k\nR2 out 0 2k\nC1 out 0 1u\n.end" with
  | .ok circuit =>
      match solveDC circuit with
      | .ok solution =>
          solution.voltages == #[5, 0, 10 / 3] &&
          solution.currents == #[-1 / 600, 1 / 600, 1 / 600, 0]
      | .error _ => false
  | .error _ => false)

#guard
  (match Spice.parseAndElaborateDC
      "hierarchy\n.subckt leaf a b\nR1 a b 1k\n.ends leaf\nV1 in 0 5\nX1 in out leaf\nRLOAD out 0 2k\n.end" with
  | .ok circuit =>
      circuit.deviceNames == #["v1", "rload", "x1.r1"] &&
      (solveDC circuit).isOk
  | .error _ => false)

#guard
  Spice.parseAndElaborateDC
    "missing subckt\nV1 in 0 5\nX1 in out absent\nR1 out 0 1k\n.end"
      matches .error _

#guard
  Spice.parseAndElaborateDC
    "bad arity\n.subckt leaf a b\nR1 a b 1k\n.ends\nV1 in 0 5\nX1 in leaf\n.end"
      matches .error _

#guard
  Spice.parseAndElaborateDC
    "recursive\n.subckt loop a b\nXSELF a b loop\n.ends\nV1 in 0 5\nX1 in out loop\nR1 out 0 1k\n.end"
      matches .error _

#guard
  (match Spice.parseAndElaborateDC
      "inconsistent\nV1 in 0 DC 1\nV2 in 0 DC 2\n.end" with
  | .ok circuit =>
      match solveDC circuit with
      | .error .inconsistent => true
      | _ => false
  | .error _ => false)

#guard
  (match Spice.parseAndElaborateDC
      "underdetermined\nV1 in 0 DC 1\nV2 in 0 DC 1\n.end" with
  | .ok circuit =>
      match solveDC circuit with
      | .error (.underdetermined _) => true
      | _ => false
  | .error _ => false)

example :
    ConservativeConnection
      [{ potential := (5 : Rat), flow := (1 : Rat) },
       { potential := (5 : Rat), flow := (-1 : Rat) }] := by
  simp [ConservativeConnection, PotentialsAgree, FlowsConserve]

#print axioms solveDC_satisfies
#print axioms directDivider_solution_satisfies

end LeanModels.Circuit.Tests
