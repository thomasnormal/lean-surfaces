import LeanModels.Spice.Surface
import LeanModels.Spice.Switch

namespace Examples.spice.and_gate.proof

open LeanModels.Spice

load_netlist andGateDeck from "Examples/spice/and_gate/and_gate.json"

/-- A reusable AND-block theorem derived only from the six MOS switch laws. -/
theorem cmos_and_from_device_laws
    {left right nand series output vdd ground : Bool}
    (hlaws : CmosAndDeviceLaws left right nand series output vdd ground)
    (hvdd : vdd = true) (hground : ground = false) :
    output = Bool.and left right := by
  rcases left with _ | _ <;> rcases right with _ | _ <;>
    simp [CmosAndDeviceLaws] at hlaws ⊢ <;> grind

/-- A satisfying internal-node assignment for each Boolean input vector. -/
private def andState (left right : Bool) : LogicState :=
  { level := fun node =>
      if node == "vdd" then true
      else if node == "a" then left
      else if node == "b" then right
      else if node == "nand" then !(left && right)
      else if node == "nseries" then left && !right
      else if node == "out" then left && right
      else false }

private theorem andGateDeviceLaws (state : LogicState)
    (hsatisfies : SwitchSatisfies andGateDeck state) :
    CmosAndDeviceLaws
      (state.level "a") (state.level "b")
      (state.level "nand") (state.level "nseries")
      (state.level "out") (state.level "vdd") (state.level "0") := by
  simpa [SwitchSatisfies, flattenSwitch, flattenSwitchCards, flattenBudget,
    SwitchCardsSatisfy, SwitchCardLaw, MosfetSwitchLaw,
    Netlist.findMosModel, andGateDeck, renameElement, renameMosfet,
    renameNode, lookupRename, qualify, CmosAndDeviceLaws] using hsatisfies

/-- The extracted six-transistor CMOS network implements Boolean AND under
the ideal-switch MOS semantics. -/
theorem cmos_and_correct :
    BinaryGateContract andGateDeck "a" "b" "out" (· && ·) := by
  intro left right
  constructor
  · intro state hsatisfies hdrives
    have hout := cmos_and_from_device_laws
      (andGateDeviceLaws state hsatisfies) hdrives.2.1 hdrives.1
    simpa [hdrives.2.2.1, hdrives.2.2.2] using hout
  · refine ⟨andState left right, ?_, ?_⟩
    · rcases left with _ | _ <;> rcases right with _ | _ <;>
        simp [SwitchSatisfies, flattenSwitch, flattenSwitchCards,
          flattenBudget, SwitchCardLaw, MosfetSwitchLaw,
          SwitchCardsSatisfy, Netlist.findMosModel, andGateDeck, andState,
          renameElement, renameMosfet, renameNode, lookupRename, qualify]
    · simp [DrivesTwo, andState]

end Examples.spice.and_gate.proof
