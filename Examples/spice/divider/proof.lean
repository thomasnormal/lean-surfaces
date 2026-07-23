import LeanModels.Spice.Surface

namespace Examples.spice.divider.proof

open LeanModels.Spice

load_netlist divider from "Examples/spice/divider/divider.json"

/-- Every DC state satisfying the extracted divider has the exact output
voltage `10/3`. -/
theorem divider_out : divider ⊨dc { v, _i => v "out" = 10 / 3 } := by
  spice_solve

/-- The extracted divider has one operating point on all supported voltages
and branch currents. -/
theorem divider_wellposed : WellPosed divider := by
  spice_solve

/-- A small safety envelope derived from the same physical equations. -/
theorem divider_safe :
    divider ⊨dc { v, _i => 0 ≤ v "out" ∧ v "out" ≤ 5 } := by
  spice_solve

end Examples.spice.divider.proof
