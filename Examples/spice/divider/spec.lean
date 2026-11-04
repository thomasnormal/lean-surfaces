import LeanModels.Python.Surface
import Examples.spice.divider.proof

open LeanModels.Circuit

load_circuit divider from "Examples/spice/divider/divider.cir"

#circuit_check divider dc shows "out" = (10 / 3 : Rat)

theorem divider_out :
    divider ⊨dc {
      v, _i => v (node! divider "out") = 10 / 3
    } := by proofs

theorem divider_realizable : RealizableDC divider := by proofs

theorem divider_wellposed : DeterminateDC divider := by proofs

theorem divider_safe :
    divider ⊨dc {
      v, _i => 0 ≤ v (node! divider "out") ∧
        v (node! divider "out") ≤ 5
    } := by proofs

#print axioms divider_out
#print axioms divider_realizable
#print axioms divider_wellposed
#print axioms divider_safe
#print axioms divider_solution_satisfies
