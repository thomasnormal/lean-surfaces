import Examples.spice.and_gate.spec
import LeanModels.Spice.Surface
import LeanModels.Spice.Cmos
import LeanModels.Spice.Mos1Logic

namespace Examples.spice.half_adder.proof

open LeanModels.Spice

load_netlist halfAdderDeck from "Examples/spice/half_adder/half_adder.json"

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

private def halfAdderMos1Flat : Netlist :=
  (flattenSwitch halfAdderDeck).toOption.getD default

private theorem halfAdder_mos1_flatten :
    flattenSwitch halfAdderDeck = .ok halfAdderMos1Flat := by
  rfl

private def instantiateMos1Subckt
    (subcktName path : String) (actuals : List String) : List Card :=
  match findSubckt halfAdderDeck.subckts subcktName with
  | none => []
  | some subckt =>
      let renames := subckt.ports.toList.zip actuals
      subckt.body.toList.map fun
        | .mosfet mosfet => .mosfet (renameMosfet path renames mosfet)
        | card => card

private def halfAdderMos1Cards : List Card :=
  instantiateMos1Subckt "and2" "xcarry" ["a", "b", "carry", "vdd"] ++
  instantiateMos1Subckt "or2" "xany" ["a", "b", "any", "vdd"] ++
  instantiateMos1Subckt "inv" "xnotcarry" ["carry", "ncarry", "vdd"] ++
  instantiateMos1Subckt "and2" "xsum" ["any", "ncarry", "sum", "vdd"] ++
  halfAdderDeck.cards.toList.drop 4 |>.dropLast

private theorem halfAdder_mos1_cards :
    halfAdderMos1Flat.cards.toList = halfAdderMos1Cards := by
  rfl

private def halfAdderNModel : MosModel :=
  { span := ⟨39, 39⟩, name := "nmod", polarity := .nmos
    parameters := #[
      ⟨"level", 1⟩, ⟨"vto", 1⟩, ⟨"kp", 1 / 10000⟩, ⟨"lambda", 0⟩,
      ⟨"is", 0⟩] }

private def halfAdderPModel : MosModel :=
  { span := ⟨40, 40⟩, name := "pmod", polarity := .pmos
    parameters := #[
      ⟨"level", 1⟩, ⟨"vto", -1⟩, ⟨"kp", 1 / 20000⟩, ⟨"lambda", 0⟩,
      ⟨"is", 0⟩] }

private noncomputable def halfAdderNParams : Mos1Params :=
  { polarity := .nmos, threshold := 1, beta := 1 / 10000, lambda := 0 }

private noncomputable def halfAdderPParams : Mos1Params :=
  { polarity := .pmos, threshold := 1, beta := 1 / 20000, lambda := 0 }

private theorem halfAdder_find_nmodel :
    halfAdderMos1Flat.findMosModelCard "nmod" = some halfAdderNModel := by
  rfl

private theorem halfAdder_find_pmodel :
    halfAdderMos1Flat.findMosModelCard "pmod" = some halfAdderPModel := by
  rfl

private theorem halfAdder_parse_nmodel :
    Mos1Params.ofModel? halfAdderNModel = some halfAdderNParams := by
  simp [halfAdderNModel, halfAdderNParams, Mos1Params.ofModel?,
    MosModel.parameter?, List.findSome?]

private theorem halfAdder_parse_pmodel :
    Mos1Params.ofModel? halfAdderPModel = some halfAdderPParams := by
  simp [halfAdderPModel, halfAdderPParams, Mos1Params.ofModel?,
    MosModel.parameter?, List.findSome?]

/-- Each hierarchical submodule's local KCL equations, extracted from the
single flattened 20-transistor deck. CMOS gate terminals draw zero current in
this MOS1 profile, so fanout does not add a term to a driving output's KCL. -/
private theorem halfAdderMos1Equations (state : Mos1CircuitState)
    (hs : Mos1Satisfies halfAdderDeck state)
    (hb : Mos1WithinSupply halfAdderDeck state)
    {left right : Bool}
    (hd : Mos1DrivesTwo state "a" "b" left right) :
    Mos1AndEquations (logicVoltage left) (logicVoltage right)
      (state.voltage "xcarry.nand") (state.voltage "xcarry.nseries")
      (state.voltage "carry") ∧
    Mos1OrEquations (logicVoltage left) (logicVoltage right)
      (state.voltage "xany.pseries") (state.voltage "xany.nor")
      (state.voltage "any") ∧
    Mos1InverterEquations (state.voltage "carry")
      (state.voltage "ncarry") ∧
    Mos1AndEquations (state.voltage "any") (state.voltage "ncarry")
      (state.voltage "xsum.nand") (state.voltage "xsum.nseries")
      (state.voltage "sum") := by
  unfold Mos1Satisfies at hs
  unfold Mos1WithinSupply at hb
  rw [halfAdder_mos1_flatten] at hs hb
  rcases hs with ⟨_, _, hkcl⟩
  have hcarryNand := hkcl "xcarry.nand" (by decide) (by decide)
  have hcarrySeries := hkcl "xcarry.nseries" (by decide) (by decide)
  have hcarry := hkcl "carry" (by decide) (by decide)
  have hOrSeries := hkcl "xany.pseries" (by decide) (by decide)
  have hNor := hkcl "xany.nor" (by decide) (by decide)
  have hAny := hkcl "any" (by decide) (by decide)
  have hNcarry := hkcl "ncarry" (by decide) (by decide)
  have hSumNand := hkcl "xsum.nand" (by decide) (by decide)
  have hSumSeries := hkcl "xsum.nseries" (by decide) (by decide)
  have hSum := hkcl "sum" (by decide) (by decide)
  have bounds (node : String)
      (hnode : node ∈ mos1Nodes halfAdderMos1Flat) :=
    hb node hnode
  have bCarryNand := bounds "xcarry.nand" (by decide)
  have bCarrySeries := bounds "xcarry.nseries" (by decide)
  have bCarry := bounds "carry" (by decide)
  have bOrSeries := bounds "xany.pseries" (by decide)
  have bNor := bounds "xany.nor" (by decide)
  have bAny := bounds "any" (by decide)
  have bNcarry := bounds "ncarry" (by decide)
  have bSumNand := bounds "xsum.nand" (by decide)
  have bSumSeries := bounds "xsum.nseries" (by decide)
  have bSum := bounds "sum" (by decide)
  unfold mos1Kcl at hcarryNand hcarrySeries hcarry hOrSeries hNor hAny hNcarry hSumNand hSumSeries hSum
  rw [halfAdder_mos1_cards] at hcarryNand hcarrySeries hcarry hOrSeries hNor hAny hNcarry hSumNand hSumSeries hSum
  simp [mos1CardCurrentLeaving, mos1DrainCurrent] at hcarryNand hcarrySeries hcarry hOrSeries hNor hAny hNcarry hSumNand hSumSeries hSum
  simp [halfAdderMos1Cards, instantiateMos1Subckt, halfAdderDeck,
    findSubckt, renameMosfet, renameNode, lookupRename, qualify] at hcarryNand hcarrySeries hcarry hOrSeries hNor hAny hNcarry hSumNand hSumSeries hSum
  simp only [halfAdder_find_nmodel, halfAdder_find_pmodel, Option.bind_some,
    halfAdder_parse_nmodel, halfAdder_parse_pmodel,
    halfAdderNParams, halfAdderPParams] at hcarryNand hcarrySeries hcarry hOrSeries hNor hAny hNcarry hSumNand hSumSeries hSum
  rcases hd with ⟨hground, hvdd, hleft, hright⟩
  simp only [hground, hvdd, hleft, hright] at hcarryNand hcarrySeries hcarry hOrSeries hNor hAny hNcarry hSumNand hSumSeries hSum
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨bCarryNand, bCarrySeries,
      ⟨bCarry, by
        simpa [Mos1InverterEquations, mos1NCurrent, mos1PCurrent] using hcarry⟩,
      by simpa [mos1NCurrent, mos1PCurrent] using hcarryNand,
      by simpa [mos1NCurrent] using hcarrySeries⟩
  · exact ⟨bOrSeries, bNor,
      ⟨bAny, by
        simpa [Mos1InverterEquations, mos1NCurrent, mos1PCurrent] using hAny⟩,
      by simpa [mos1NCurrent, mos1PCurrent] using hOrSeries,
      by simpa [mos1NCurrent, mos1PCurrent] using hNor⟩
  · exact ⟨bNcarry, by
      simpa [mos1NCurrent, mos1PCurrent] using hNcarry⟩
  · exact ⟨bSumNand, bSumSeries,
      ⟨bSum, by
        simpa [Mos1InverterEquations, mos1NCurrent, mos1PCurrent] using hSum⟩,
      by simpa [mos1NCurrent, mos1PCurrent] using hSumNand,
      by simpa [mos1NCurrent] using hSumSeries⟩

/-- The extracted 20-transistor hierarchy implements a half-adder directly
from its ngspice Level-1 equations and KCL. Both AND instances reuse
`mos1_and_from_equations`; no ideal-switch premise occurs in this theorem. -/
theorem half_adder_mos1_correct :
    Mos1HalfAdderContract halfAdderDeck "a" "b" "sum" "carry" := by
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
