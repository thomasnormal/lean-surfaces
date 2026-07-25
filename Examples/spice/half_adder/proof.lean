import Examples.spice.and_gate.spec
import LeanModels.Circuit.Surface
import LeanModels.Spice.Mos1Surface
import LeanModels.Spice.Mos1Logic

namespace Examples.spice.half_adder.proof

open LeanModels.Spice

load_circuit halfAdderDeck from "Examples/spice/half_adder/half_adder.cir"

/-- Boolean rail assignment used only to exhibit non-vacuity witnesses. -/
private def halfAdderLevel (left right : Bool) (name : String) : Bool :=
  let carry := Bool.and left right
  let any := Bool.or left right
  let ncarry := !carry
  let sum := Bool.xor left right
  if name == "vdd" then true
  else if name == "a" then left
  else if name == "b" then right
  else if name == "carry" then carry
  else if name == "xcarry.nand" then !carry
  else if name == "xcarry.nseries" then Bool.and left (!right)
  else if name == "any" then any
  else if name == "xany.nor" then !any
  else if name == "xany.pseries" then !left
  else if name == "ncarry" then ncarry
  else if name == "sum" then sum
  else if name == "xsum.nand" then !(Bool.and any ncarry)
  else if name == "xsum.nseries" then Bool.and any (!ncarry)
  else false


def halfAdderMos1 : Mos1ResolvedCircuit :=
  halfAdderDeck_mos1

/-- Each hierarchical submodule's local KCL equations, extracted from the
single flattened 20-transistor deck. CMOS gate terminals draw zero current in
this MOS1 profile, so fanout does not add a term to a driving output's KCL. -/
private theorem halfAdderMos1Equations (state : Mos1CircuitState)
    (hs : Mos1ComponentSatisfies halfAdderMos1
      [supply, node "a", node "b"] state)
    (hb : Mos1WithinSupply halfAdderMos1 state)
    {left right : Bool}
    (hd : Mos1DrivesTwo state
      (mos_node! halfAdderMos1 "a") (mos_node! halfAdderMos1 "b") left right) :
    Mos1AndEquations (logicVoltage left) (logicVoltage right)
      (state.voltage (node "xcarry.nand"))
      (state.voltage (node "xcarry.nseries"))
      (state.voltage (node "carry")) ∧
    Mos1OrEquations (logicVoltage left) (logicVoltage right)
      (state.voltage (node "xany.pseries"))
      (state.voltage (node "xany.nor"))
      (state.voltage (node "any")) ∧
    Mos1InverterEquations (state.voltage (node "carry"))
      (state.voltage (node "ncarry")) ∧
    Mos1AndEquations (state.voltage (node "any"))
      (state.voltage (node "ncarry"))
      (state.voltage (node "xsum.nand"))
      (state.voltage (node "xsum.nseries"))
      (state.voltage (node "sum")) := by
  mos1_extract hs hb at halfAdderMos1 [
    "xcarry.nand" => hcarryNand, bCarryNand,
    "xcarry.nseries" => hcarrySeries, bCarrySeries,
    "carry" => hcarry, bCarry,
    "xany.pseries" => hOrSeries, bOrSeries,
    "xany.nor" => hNor, bNor,
    "any" => hAny, bAny,
    "ncarry" => hNcarry, bNcarry,
    "xsum.nand" => hSumNand, bSumNand,
    "xsum.nseries" => hSumSeries, bSumSeries,
    "sum" => hSum, bSum]
  unfold mos1Kcl at hcarryNand hcarrySeries hcarry hOrSeries hNor hAny hNcarry hSumNand hSumSeries hSum
  simp [halfAdderMos1, halfAdderDeck_mos1,
    mos1DeviceCurrentLeaving,
    mos1DrainCurrent, Mos1Model.params, node] at hcarryNand hcarrySeries hcarry hOrSeries hNor hAny hNcarry hSumNand hSumSeries hSum
  rcases hd with ⟨hground, hvdd, hleft, hright⟩
  have hground' : state.voltage ⟨"0"⟩ = 0 := by
    simpa [ground, node] using hground
  have hvdd' : state.voltage ⟨"vdd"⟩ = 5 := by
    simpa [supply, node] using hvdd
  have hleft' : state.voltage ⟨"a"⟩ = logicVoltage left := by
    simpa [node] using hleft
  have hright' : state.voltage ⟨"b"⟩ = logicVoltage right := by
    simpa [node] using hright
  simp only [hground', hvdd', hleft', hright'] at hcarryNand hcarrySeries hcarry hOrSeries hNor hAny hNcarry hSumNand hSumSeries hSum
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨bCarryNand, bCarrySeries,
      ⟨bCarry, by
        simpa [Mos1InverterEquations, mos1NCurrent, mos1PCurrent, node]
          using hcarry⟩,
      by simpa [mos1NCurrent, mos1PCurrent, node] using hcarryNand,
      by simpa [mos1NCurrent, node] using hcarrySeries⟩
  · exact ⟨bOrSeries, bNor,
      ⟨bAny, by
        simpa [Mos1InverterEquations, mos1NCurrent, mos1PCurrent, node]
          using hAny⟩,
      by simpa [mos1NCurrent, mos1PCurrent, node] using hOrSeries,
      by simpa [mos1NCurrent, mos1PCurrent, node] using hNor⟩
  · exact ⟨bNcarry, by
      simpa [mos1NCurrent, mos1PCurrent, node] using hNcarry⟩
  · exact ⟨bSumNand, bSumSeries,
      ⟨bSum, by
        simpa [Mos1InverterEquations, mos1NCurrent, mos1PCurrent, node]
          using hSum⟩,
      by simpa [mos1NCurrent, mos1PCurrent, node] using hSumNand,
      by simpa [mos1NCurrent, node] using hSumSeries⟩

/-- The extracted 20-transistor hierarchy implements a half-adder directly
from its ngspice Level-1 equations and KCL. Both AND instances reuse
`mos1_and_from_equations`; no ideal-switch premise occurs in this theorem. -/
theorem half_adder_mos1_correct :
    Mos1HalfAdderContract halfAdderMos1
      (mos_node! halfAdderMos1 "a") (mos_node! halfAdderMos1 "b")
      (mos_node! halfAdderMos1 "sum") (mos_node! halfAdderMos1 "carry") := by
  intro left right state hs hb hd
  rcases halfAdderMos1Equations state hs hb hd with
    ⟨hcarryEq, horEq, hinverterEq, hsumEq⟩
  have hcarry := mos1_and_from_equations hcarryEq
  have hany := mos1_or_from_equations horEq
  have hncarry := mos1_inverter_from_equations hcarry hinverterEq
  rw [hany, hncarry] at hsumEq
  have hsum := mos1_and_from_equations hsumEq
  constructor
  · rcases left with _ | _ <;> rcases right with _ | _ <;>
      simpa [logicVoltage] using hsum
  · exact hcarry

/-- Exact rail-valued state used to show that the open MOS1 component
contract is non-vacuous for every Boolean input vector. -/
private noncomputable def halfAdderMos1Witness
    (left right : Bool) : Mos1CircuitState :=
  { voltage := fun target =>
      logicVoltage (halfAdderLevel left right target.name)
    sourceCurrent := fun _ => 0 }

set_option maxHeartbeats 1000000 in
theorem half_adder_mos1_observation_exists (left right : Bool) :
    Mos1HalfAdderObservation halfAdderMos1
      (mos_node! halfAdderMos1 "a") (mos_node! halfAdderMos1 "b")
      (mos_node! halfAdderMos1 "sum") (mos_node! halfAdderMos1 "carry")
      left right (Bool.xor left right) (Bool.and left right) := by
  refine ⟨halfAdderMos1Witness left right, ?_, ?_, ?_, ?_, ?_⟩
  · rcases left with _ | _ <;> rcases right with _ | _
    all_goals
      simp [Mos1ComponentSatisfies,
        halfAdderMos1Witness, halfAdderMos1,
        halfAdderDeck_mos1, halfAdderLevel, mos1Nodes, Mos1ResolvedCircuit.nodes,
        Mos1Device.nodes, Mos1DeviceLaw, mos1Kcl, mos1DeviceCurrentLeaving,
        mos1DrainCurrent, Mos1Model.params, mos1ForwardCurrent, logicVoltage,
        ground, supply, node] <;> norm_num
  · rcases left with _ | _ <;> rcases right with _ | _
    all_goals
      simp [Mos1WithinSupply,
        halfAdderMos1Witness, halfAdderMos1,
        halfAdderDeck_mos1, halfAdderLevel, mos1Nodes, Mos1ResolvedCircuit.nodes,
        Mos1Device.nodes, logicVoltage]
  · rcases left with _ | _ <;> rcases right with _ | _
    all_goals
      simp [Mos1DrivesTwo,
        halfAdderMos1Witness, halfAdderMos1,
        halfAdderDeck_mos1, halfAdderLevel, logicVoltage,
        ground, supply, node]
  all_goals
    rcases left with _ | _ <;> rcases right with _ | _
    all_goals
      simp [
      halfAdderMos1Witness, halfAdderMos1,
        halfAdderDeck_mos1, halfAdderLevel, logicVoltage, node]

end Examples.spice.half_adder.proof
