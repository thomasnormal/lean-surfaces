import Examples.spice.and_gate.spec
import LeanModels.Spice.Surface
import LeanModels.Spice.Cmos
import LeanModels.Spice.Mos1Logic

namespace Examples.spice.half_adder.proof

open LeanModels.Spice

load_mos1 halfAdderDeck from "Examples/spice/half_adder/half_adder.json"

/-- The computed, hierarchy-free switch deck. -/
private def halfAdderSwitchFlat : Netlist :=
  (flattenSwitch halfAdderDeck).toOption.getD default

private theorem halfAdder_flattenSwitch :
    flattenSwitch halfAdderDeck = .ok halfAdderSwitchFlat := by
  rfl

/-- The six switch implications contributed by a CMOS NOR followed by an
inverter. -/
private def CmosOrDeviceLaws
    (left right series nor output vdd ground : Bool) : Prop :=
  (left = false → series = vdd) ∧
  (right = false → nor = series) ∧
  (left = true → nor = ground) ∧
  (right = true → nor = ground) ∧
  (nor = false → output = vdd) ∧
  (nor = true → output = ground)

private theorem cmos_or_from_device_laws
    {left right series nor output vdd ground : Bool}
    (hlaws : CmosOrDeviceLaws left right series nor output vdd ground)
    (hvdd : vdd = true) (hground : ground = false) :
    output = Bool.or left right := by
  rcases left with _ | _ <;> rcases right with _ | _ <;>
    simp [CmosOrDeviceLaws] at hlaws ⊢ <;> grind

/-- The two switch implications contributed by a CMOS inverter. -/
private def CmosInverterDeviceLaws
    (input output vdd ground : Bool) : Prop :=
  (input = false → output = vdd) ∧
  (input = true → output = ground)

private theorem cmos_inverter_from_device_laws
    {input output vdd ground : Bool}
    (hlaws : CmosInverterDeviceLaws input output vdd ground)
    (hvdd : vdd = true) (hground : ground = false) :
    output = !input := by
  rcases input with _ | _ <;>
    simp [CmosInverterDeviceLaws] at hlaws ⊢ <;> grind

/-- The four physical submodule contracts read from the flattened hierarchy. -/
private def HalfAdderDeviceLaws (state : LogicState) : Prop :=
  CmosAndDeviceLaws
      (state.level "a") (state.level "b")
      (state.level "xcarry.nand") (state.level "xcarry.nseries")
      (state.level "carry") (state.level "vdd") (state.level "0") ∧
  CmosOrDeviceLaws
      (state.level "a") (state.level "b")
      (state.level "xany.pseries") (state.level "xany.nor")
      (state.level "any") (state.level "vdd") (state.level "0") ∧
  CmosInverterDeviceLaws
      (state.level "carry") (state.level "ncarry")
      (state.level "vdd") (state.level "0") ∧
  CmosAndDeviceLaws
      (state.level "any") (state.level "ncarry")
      (state.level "xsum.nand") (state.level "xsum.nseries")
      (state.level "sum") (state.level "vdd") (state.level "0")

private theorem halfAdderDeviceLaws (state : LogicState)
    (hsatisfies : SwitchSatisfies halfAdderDeck state) :
    HalfAdderDeviceLaws state := by
  unfold SwitchSatisfies at hsatisfies
  rw [halfAdder_flattenSwitch] at hsatisfies
  dsimp [halfAdderSwitchFlat, flattenSwitch, flattenSwitchCards,
    flattenBudget, halfAdderDeck, renameElement, renameMosfet, renameNode,
    lookupRename, qualify, findSubckt] at hsatisfies
  simpa [Except.bind, Except.pure, Except.instMonad, Bind.bind, Pure.pure,
    Option.getD, Except.toOption, List.append, List.findSome?,
    SwitchCardsSatisfy, SwitchCardLaw,
    MosfetSwitchLaw, and_assoc,
    Netlist.findMosModel, HalfAdderDeviceLaws, CmosAndDeviceLaws,
    CmosOrDeviceLaws, CmosInverterDeviceLaws,
    flattenSwitch, flattenSwitchCards, flattenBudget, halfAdderDeck,
    renameElement, renameMosfet, renameNode, lookupRename, qualify,
    findSubckt] using hsatisfies

/-- One concrete internal-node realization for each input vector. -/
private def halfAdderState (left right : Bool) : LogicState :=
  let carry := Bool.and left right
  let any := Bool.or left right
  let ncarry := !carry
  let sum := Bool.xor left right
  { level := fun node =>
      if node == "vdd" then true
      else if node == "a" then left
      else if node == "b" then right
      else if node == "carry" then carry
      else if node == "xcarry.nand" then !carry
      else if node == "xcarry.nseries" then Bool.and left (!right)
      else if node == "any" then any
      else if node == "xany.nor" then !any
      else if node == "xany.pseries" then !left
      else if node == "ncarry" then ncarry
      else if node == "sum" then sum
      else if node == "xsum.nand" then !(Bool.and any ncarry)
      else if node == "xsum.nseries" then Bool.and any (!ncarry)
      else false }

/-- The extracted hierarchical transistor network implements a one-bit
half-adder. Both AND instances reuse `cmos_and_from_device_laws`. -/
theorem half_adder_correct :
    HalfAdderContract halfAdderDeck "a" "b" "sum" "carry" := by
  intro left right
  constructor
  · intro state hsatisfies hdrives
    rcases halfAdderDeviceLaws state hsatisfies with
      ⟨hcarryLaws, horLaws, hinverterLaws, hsumLaws⟩
    have hcarry := cmos_and_from_device_laws
      hcarryLaws hdrives.2.1 hdrives.1
    have hany := cmos_or_from_device_laws
      horLaws hdrives.2.1 hdrives.1
    have hncarry := cmos_inverter_from_device_laws
      hinverterLaws hdrives.2.1 hdrives.1
    have hsum := cmos_and_from_device_laws
      hsumLaws hdrives.2.1 hdrives.1
    rw [hdrives.2.2.1, hdrives.2.2.2] at hcarry hany
    rw [hcarry] at hncarry
    rw [hany, hncarry] at hsum
    constructor
    · rcases left with _ | _ <;> rcases right with _ | _ <;>
        simpa using hsum
    · exact hcarry
  · refine ⟨halfAdderState left right, ?_, ?_⟩
    · rcases left with _ | _ <;> rcases right with _ | _ <;>
        unfold SwitchSatisfies <;>
        rw [halfAdder_flattenSwitch] <;>
        dsimp [halfAdderSwitchFlat, flattenSwitch, flattenSwitchCards,
          flattenBudget, halfAdderDeck, renameElement, renameMosfet,
          renameNode, lookupRename, qualify, findSubckt] <;>
        simp [Except.bind, Except.pure, Bind.bind, Pure.pure,
          Option.getD, Except.toOption, List.findSome?,
          SwitchCardsSatisfy, SwitchCardLaw,
          MosfetSwitchLaw, Netlist.findMosModel, halfAdderState,
          flattenSwitchCards,
          renameElement, renameMosfet, renameNode, lookupRename, qualify,
          findSubckt]
    · simp [DrivesTwo, halfAdderState]

/-- Exact two-way interface abstraction of the proved transistor block. -/
theorem half_adder_interface
    {left right sum carry : Bool} :
    HalfAdderObservation halfAdderDeck "a" "b" "sum" "carry"
        left right sum carry ↔
      HalfAdderBehavior left right sum carry := by
  constructor
  · rintro ⟨state, hsatisfies, hdrives, hsum, hcarry⟩
    have houtputs :=
      (half_adder_correct left right).1 state hsatisfies hdrives
    exact ⟨hsum.symm.trans houtputs.1, hcarry.symm.trans houtputs.2⟩
  · rintro ⟨hsum, hcarry⟩
    rcases (half_adder_correct left right).2 with
      ⟨state, hsatisfies, hdrives⟩
    have houtputs :=
      (half_adder_correct left right).1 state hsatisfies hdrives
    exact ⟨state, hsatisfies, hdrives,
      houtputs.1.trans hsum.symm, houtputs.2.trans hcarry.symm⟩

/-! ## Ngspice MOS Level 1 proof -/

def halfAdderMos1 : Mos1Circuit :=
  halfAdderDeck_mos1

/-- Each hierarchical submodule's local KCL equations, extracted from the
single flattened 20-transistor deck. CMOS gate terminals draw zero current in
this MOS1 profile, so fanout does not add a term to a driving output's KCL. -/
private theorem halfAdderMos1Equations (state : Mos1CircuitState)
    (hs : Mos1Satisfies halfAdderMos1 state)
    (hb : Mos1WithinSupply halfAdderMos1 state)
    {left right : Bool}
    (hd : Mos1DrivesTwo state
      (node! halfAdderMos1 "a") (node! halfAdderMos1 "b") left right) :
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
  simp [halfAdderMos1, halfAdderDeck_mos1, mos1DeviceCurrentLeaving,
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
      (node! halfAdderMos1 "a") (node! halfAdderMos1 "b")
      (node! halfAdderMos1 "sum") (node! halfAdderMos1 "carry") := by
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

end Examples.spice.half_adder.proof
