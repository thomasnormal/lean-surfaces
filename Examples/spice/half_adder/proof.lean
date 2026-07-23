import Examples.spice.and_gate.spec
import LeanModels.Spice.Surface
import LeanModels.Spice.Switch

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

end Examples.spice.half_adder.proof
