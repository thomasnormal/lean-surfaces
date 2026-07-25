import LeanModels.Circuit

namespace Examples.spice.divider.proof

open LeanModels.Circuit

load_circuit divider from "Examples/spice/divider/divider.cir"

/-- Every DC state satisfying ground, the source law, Ohm's law, and KCL has
the exact divider output voltage. -/
theorem divider_out :
    divider ⊨dc {
      v, _i => v (node! divider "out") = 10 / 3
    } := by
  circuit_dc

/-- The universal voltage theorem has an explicit operating-point witness. -/
theorem divider_realizable : RealizableDC divider := by
  circuit_dc

/-- The complete voltage-and-current assignment is unique. -/
theorem divider_wellposed : DeterminateDC divider := by
  circuit_dc

/-- A small safety envelope derived from the same physical equations. -/
theorem divider_safe :
    divider ⊨dc {
      v, _i => 0 ≤ v (node! divider "out") ∧
        v (node! divider "out") ≤ 5
    } := by
  circuit_dc

end Examples.spice.divider.proof
