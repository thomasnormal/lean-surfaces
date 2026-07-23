import LeanModels.Spice.Surface
import LeanModels.Spice.Switch

namespace Examples.spice.and_gate.proof

open LeanModels.Spice

load_netlist andGateDeck from "Examples/spice/and_gate/and_gate.json"

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

/-- The extracted six-transistor CMOS network implements Boolean AND under
the ideal-switch MOS semantics. -/
theorem cmos_and_correct :
    BinaryGateContract andGateDeck "a" "b" "out" (· && ·) := by
  intro left right
  constructor
  · intro state hsatisfies hdrives
    rcases left with _ | _ <;> rcases right with _ | _
    all_goals
      simp [SwitchSatisfies, SwitchCardLaw, MosfetSwitchLaw,
        SwitchCardsSatisfy, Netlist.findMosModel, andGateDeck] at hsatisfies
      simp [DrivesTwo] at hdrives
      grind
  · refine ⟨andState left right, ?_, ?_⟩
    · rcases left with _ | _ <;> rcases right with _ | _ <;>
        simp [SwitchSatisfies, SwitchCardLaw, MosfetSwitchLaw,
          SwitchCardsSatisfy, Netlist.findMosModel, andGateDeck, andState]
    · simp [DrivesTwo, andState]

end Examples.spice.and_gate.proof
