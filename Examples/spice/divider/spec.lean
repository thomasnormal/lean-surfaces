import Examples.spice.divider.proof

open LeanModels.Spice

load_netlist divider from "Examples/spice/divider/divider.json"

#spice_check divider shows "out" = (10 / 3 : Rat)

theorem divider_out : divider ⊨dc { v, _i => v "out" = 10 / 3 } := by proofs

theorem divider_wellposed : WellPosed divider := by proofs

theorem divider_safe :
    divider ⊨dc { v, _i => 0 ≤ v "out" ∧ v "out" ≤ 5 } := by proofs

#print axioms divider_out

#print axioms divider_wellposed

#print axioms divider_safe

#print axioms divider_solution_satisfies
