import LeanModels.Spice.Compose
import LeanModels.Spice.Surface
import LeanModels.Spice.Switch

namespace LeanModels.Spice

load_netlist dividerFixture from "Examples/spice/divider/divider.json"
load_netlist chainFixture from "Examples/spice/chain/chain.json"
load_netlist r2rFixture from "Examples/spice/r2r/r2r.json"
load_mos1 andGateFixture from "Examples/spice/and_gate/and_gate.json"
load_mos1 halfAdderFixture from "Examples/spice/half_adder/half_adder.json"
load_mos1 rippleAdderFixture from "Examples/spice/ripple_adder/ripple_adder.json"

#guard dividerFixture.hasUnsupported == false
#guard chainFixture.hasUnsupported == false
#guard r2rFixture.hasUnsupported == false
#guard andGateFixture.hasUnsupported == false
#guard halfAdderFixture.hasUnsupported == false
#guard rippleAdderFixture.hasUnsupported == false

#guard andGateFixture_mos1.devices.size == 9
#guard halfAdderFixture_mos1.devices.size == 23
#guard rippleAdderFixture_mos1.devices.size == 250
#guard node! andGateFixture_mos1 "out" == node "out"
#guard andGateFixture_mos1.nodeNames.contains "nseries"

#guard match andGateFixture_mos1.devices[0]? with
  | some (Mos1Device.transistor transistor) =>
      transistor.id == transistorId "mpa" &&
      transistor.drain == node "nand" &&
      transistor.gate == node "a" &&
      transistor.source == supply &&
      transistor.bulk == supply &&
      transistor.model.id == modelId "pmod" &&
      transistor.model.polarity == .pmos &&
      transistor.model.threshold == 1 &&
      transistor.model.transconductance == (1 / 20000 : Rat)
  | _ => false

private def unresolvedModelFixture : Netlist :=
  { title := "unresolved model"
    subckts := #[]
    cards := #[
      .mosfet {
        span := ⟨1, 1⟩
        name := "m1"
        drain := "out"
        gate := "in"
        source := "0"
        bulk := "0"
        model := "missing" }] }

#guard match unresolvedModelFixture.toMos1 with
  | .error (.missingModel device model) =>
      device == transistorId "m1" && model == modelId "missing"
  | _ => false

private def invalidLevelFixture : Netlist :=
  { title := "invalid model level"
    subckts := #[]
    cards := #[
      .mosModel {
        span := ⟨1, 1⟩
        name := "nmod"
        polarity := .nmos
        parameters := #[⟨"level", 2⟩] }] }

#guard match invalidLevelFixture.toMos1 with
  | .error (.invalidModel model) => model == modelId "nmod"
  | _ => false

example (state : Mos1CircuitState)
    (hs : Mos1Satisfies andGateFixture_mos1 state)
    (hb : Mos1WithinSupply andGateFixture_mos1 state) :
    mos1Kcl andGateFixture_mos1 state (node "out") = 0 ∧
      0 ≤ state.voltage (node "out") ∧ state.voltage (node "out") ≤ 5 := by
  mos1_extract hs hb at andGateFixture_mos1 [
    "out" => hout, bout]
  exact ⟨hout, bout⟩

#guard match flattenSwitch halfAdderFixture with
  | .ok flat => halfAdderFixture.subckts.size == 3 &&
      flat.subckts.isEmpty && flat.cards.size == 25
  | .error _ => false

#guard match andGateFixture.cards[0]? with
  | some (Card.mosfet mosfet) =>
      mosfet.name == "mpa" && mosfet.gate == "a" &&
        mosfet.model == "pmod"
  | _ => false

#guard match andGateFixture.findMosModel "nmod" with
  | some .nmos => true
  | _ => false

#guard match flatten andGateFixture with
  | .error (.unsupported "M" _) => true
  | _ => false

#guard match flatten dividerFixture with
  | .ok flat => flat.elements.size == 3 &&
      match solve flat with
      | .ok assignment => assignment.volt "out" == (10 / 3 : Rat)
      | .error _ => false
  | .error _ => false

#guard dividerFixture_solution.describe ==
  "V(in) = 5\nV(out) = 10/3\nI(v1) = -1/600"

#guard (assemble dividerFixture_flat).describe ==
  "unknowns: V(in), V(out), I(v1)\n" ++
  "[-1/1000, 1/1000, -1] = 0\n" ++
  "[1/1000, -3/2000, 0] = 0\n" ++
  "[1, 0, 0] = 5"

#guard match flatten chainFixture with
  | .ok flat => flat.elements.size == 16 &&
      match solve flat with
      | .ok assignment =>
          assignment.volt "out1" == (10 / 3 : Rat) &&
          assignment.volt "out2" == (20 / 9 : Rat) &&
          assignment.volt "out3" == (40 / 27 : Rat)
      | .error _ => false
  | .error _ => false

#guard match flatten r2rFixture with
  | .ok flat => flat.elements.size == 12 &&
      match solve flat with
      | .ok assignment => assignment.volt "out" == (25 / 8 : Rat)
      | .error _ => false
  | .error _ => false

private abbrev port0 : Fin 2 := ⟨0, by decide⟩
private abbrev port1 : Fin 2 := ⟨1, by decide⟩

/- The computable basis reduction agrees with the section's hand-derived
two-port admittance matrix exactly, not merely within a numeric tolerance. -/
#guard match chainFixture.subckts[0]? with
  | some (SubcktEntry.definition subckt) =>
      match reduceLeaf subckt 2 with
      | .ok contract =>
          contract.Y port0 port0 == (1 / 1000 : Rat) &&
          contract.Y port0 port1 == (-1 / 1000 : Rat) &&
          contract.Y port1 port0 == (-1 / 1000 : Rat) &&
          contract.Y port1 port1 == (7 / 6000 : Rat) &&
          contract.J port0 == 0 && contract.J port1 == 0
      | .error _ => false
  | _ => false

#print axioms solve_satisfies
#print axioms solution_satisfies
#print axioms cascade_contracts
#print axioms compose_contracts
#print axioms tellegen_nodal
#print axioms Mos1Satisfies.kclAt
#print axioms Mos1WithinSupply.boundsAt

end LeanModels.Spice
