import LeanModels.Circuit.Surface
import LeanModels.Spice.Mos1Surface
import LeanModels.Spice.Mos1Logic

namespace Examples.spice.and_gate.proof

-- Loudness guard (family-architecture.md §autoImplicit ruling, 2026-08-24):
-- without this a mistyped or unopened name is silently auto-bound as an
-- implicit variable rather than reported. This file is monomorphic --
-- no `Type`/`Sort` binders, no generic type variables -- so the flip is
-- inert here, and it is file-local: importers are unaffected.
set_option autoImplicit false

open LeanModels.Spice

load_circuit andGateDeck from "Examples/spice/and_gate/and_gate.cir"

def andGateMos1 : Mos1ResolvedCircuit :=
  andGateDeck_mos1

private noncomputable def nCurrent (vgs vds : ℝ) : ℝ :=
  mos1ForwardCurrent
    { polarity := .nmos, threshold := 1, beta := 1 / 10000, lambda := 0 }
    vgs vds

private noncomputable def pCurrent (vsg vsd : ℝ) : ℝ :=
  mos1ForwardCurrent
    { polarity := .pmos, threshold := 1, beta := 1 / 20000, lambda := 0 }
    vsg vsd

/-- KCL at the three internal nodes, reduced from the literal extracted deck.
The coefficients come from its exact `KP`, `VTO`, and `LAMBDA` parameters. -/
private theorem andMos1_equations (state : Mos1CircuitState)
    (hs : Mos1ComponentSatisfies andGateMos1
      [supply, node "a", node "b"] state)
    (hb : Mos1WithinSupply andGateMos1 state) :
    (0 ≤ state.voltage (node "nand") ∧
      state.voltage (node "nand") ≤ 5) ∧
    (0 ≤ state.voltage (node "nseries") ∧
      state.voltage (node "nseries") ≤ 5) ∧
    (0 ≤ state.voltage (node "out") ∧
      state.voltage (node "out") ≤ 5) ∧
    (-pCurrent (state.voltage supply - state.voltage (node "a"))
          (state.voltage supply - state.voltage (node "nand")) +
        -pCurrent (state.voltage supply - state.voltage (node "b"))
          (state.voltage supply - state.voltage (node "nand")) +
        nCurrent (state.voltage (node "a") -
            state.voltage (node "nseries"))
          (state.voltage (node "nand") -
            state.voltage (node "nseries")) = 0) ∧
    (-nCurrent (state.voltage (node "a") -
          state.voltage (node "nseries"))
          (state.voltage (node "nand") -
            state.voltage (node "nseries")) +
        nCurrent (state.voltage (node "b") - state.voltage ground)
          (state.voltage (node "nseries") - state.voltage ground) = 0) ∧
    (-pCurrent (state.voltage supply - state.voltage (node "nand"))
          (state.voltage supply - state.voltage (node "out")) +
        nCurrent (state.voltage (node "nand") - state.voltage ground)
      (state.voltage (node "out") - state.voltage ground) = 0) := by
  mos1_extract hs hb at andGateMos1 [
    "nand" => hnand, bnand,
    "nseries" => hnseries, bnseries,
    "out" => hout, bout]
  unfold mos1Kcl at hnand hnseries hout
  simp [andGateMos1, andGateDeck_mos1,
    mos1DeviceCurrentLeaving, mos1DrainCurrent,
    Mos1Model.params, node] at hnand hnseries hout
  exact ⟨bnand, bnseries, bout,
    by simpa [nCurrent, pCurrent, node, supply] using hnand,
    by simpa [nCurrent, node, ground] using hnseries,
    by simpa [nCurrent, pCurrent, node, ground, supply] using hout⟩

/-- The extracted six-transistor deck implements AND directly from the
ngspice Level-1 channel equations, voltage-source laws, and KCL. The supply
envelope is an explicit premise rather than an unproved device abstraction. -/
theorem cmos_and_mos1_correct :
    Mos1BinaryGateContract andGateMos1
      (mos_node! andGateMos1 "a") (mos_node! andGateMos1 "b")
      (mos_node! andGateMos1 "out") (· && ·) := by
  intro left right state hs hb hd
  rcases andMos1_equations state hs hb with
    ⟨bnand, bnseries, bout, hnand, hnseries, hout⟩
  rcases hd with ⟨hground, hvdd, hleft, hright⟩
  simp only [hground, hvdd, hleft, hright] at hnand hnseries hout
  apply mos1_and_from_equations
  exact ⟨bnand, bnseries,
    ⟨bout, by
      simpa [nCurrent, pCurrent, mos1NCurrent, mos1PCurrent] using hout⟩,
    by simpa [nCurrent, pCurrent, mos1NCurrent, mos1PCurrent] using hnand,
    by simpa [nCurrent, mos1NCurrent] using hnseries⟩

/-- Boolean rail assignment used only to exhibit non-vacuity witnesses.

`nseries` is the node between the two series pull-down NMOS devices. It sits
at the rail `a ∧ ¬b`: with `a` high and `b` low the upper device is
source-follower-off and the lower one is cut off, so the node holds the
supply rail; in every other vector it is pulled to ground or carries no
current. The same assignment appears as `xcarry.nseries` in the half-adder,
whose `and2` subcircuit is this deck. -/
private def andGateLevel (left right : Bool) (name : String) : Bool :=
  if name == "vdd" then true
  else if name == "a" then left
  else if name == "b" then right
  else if name == "nand" then !(Bool.and left right)
  else if name == "nseries" then Bool.and left (!right)
  else if name == "out" then Bool.and left right
  else false

/-- Exact rail-valued state used to show that the open MOS1 component
contract is non-vacuous for every Boolean input vector. -/
private noncomputable def andGateMos1Witness
    (left right : Bool) : Mos1CircuitState :=
  { voltage := fun target =>
      logicVoltage (andGateLevel left right target.name)
    sourceCurrent := fun _ => 0 }

set_option maxHeartbeats 1000000 in
/-- `cmos_and_mos1_correct` is universally quantified over states satisfying
the MOS1 equations, the supply envelope and the input drivers; on its own it
would hold vacuously if no such state existed. This exhibits one for each of
the four input vectors, so the contract is a claim this deck could have
contradicted. -/
theorem and_gate_mos1_observation_exists (left right : Bool) :
    Mos1BinaryGateObservation andGateMos1
      (mos_node! andGateMos1 "a") (mos_node! andGateMos1 "b")
      (mos_node! andGateMos1 "out") left right (Bool.and left right) := by
  refine ⟨andGateMos1Witness left right, ?_, ?_, ?_, ?_⟩
  · rcases left with _ | _ <;> rcases right with _ | _
    all_goals
      simp [Mos1ComponentSatisfies,
        andGateMos1Witness, andGateMos1,
        andGateDeck_mos1, andGateLevel, mos1Nodes, Mos1ResolvedCircuit.nodes,
        Mos1Device.nodes, Mos1DeviceLaw, mos1Kcl, mos1DeviceCurrentLeaving,
        mos1DrainCurrent, Mos1Model.params, mos1ForwardCurrent, logicVoltage,
        ground, supply, node] <;> norm_num
  · rcases left with _ | _ <;> rcases right with _ | _
    all_goals
      simp [Mos1WithinSupply,
        andGateMos1Witness, andGateMos1,
        andGateDeck_mos1, andGateLevel, mos1Nodes, Mos1ResolvedCircuit.nodes,
        Mos1Device.nodes, logicVoltage]
  · rcases left with _ | _ <;> rcases right with _ | _
    all_goals
      simp [Mos1DrivesTwo,
        andGateMos1Witness, andGateMos1,
        andGateDeck_mos1, andGateLevel, logicVoltage,
        ground, supply, node]
  all_goals
    rcases left with _ | _ <;> rcases right with _ | _
    all_goals
      simp [andGateMos1Witness, andGateMos1,
        andGateDeck_mos1, andGateLevel, logicVoltage, node]

end Examples.spice.and_gate.proof
