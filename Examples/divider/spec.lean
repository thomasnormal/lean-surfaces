import Examples.divider.proof

open LeanModels.Spice

load_netlist divider from "Examples/divider/divider.json"

#spice_check divider shows "out" = (10 / 3 : Rat)

theorem divider_out : divider ⊨dc { v, _i => v "out" = 10 / 3 } := by proofs

theorem divider_wellposed : WellPosed divider := by proofs

#print axioms divider_out

#print axioms divider_wellposed
