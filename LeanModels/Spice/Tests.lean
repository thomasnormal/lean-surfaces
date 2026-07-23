import LeanModels.Spice.Compose
import LeanModels.Spice.Surface
import LeanModels.Spice.Switch

namespace LeanModels.Spice

load_netlist dividerFixture from "Examples/spice/divider/divider.json"
load_netlist chainFixture from "Examples/spice/chain/chain.json"
load_netlist r2rFixture from "Examples/spice/r2r/r2r.json"
load_netlist andGateFixture from "Examples/spice/and_gate/and_gate.json"

#guard dividerFixture.hasUnsupported == false
#guard chainFixture.hasUnsupported == false
#guard r2rFixture.hasUnsupported == false
#guard andGateFixture.hasUnsupported == false

#guard match andGateFixture.cards[0]? with
  | some (.mosfet mosfet) =>
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

end LeanModels.Spice
