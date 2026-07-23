import Examples.spice.r2r.proof

open LeanModels.Spice
open Examples.spice.r2r.proof

private def bits1010 : Fin 4 → Bool
  | ⟨0, _⟩ => false
  | ⟨1, _⟩ => true
  | ⟨2, _⟩ => false
  | ⟨3, _⟩ => true

#spice_check r2rCircuit bits1010 shows "out" = (25 / 8 : Rat)

theorem r2r_guarantee (bits : Fin 4 → Bool) :
    r2rCircuit bits ⊨dc { v, _i => v "out" = 5 * binVal bits / 16 } := by proofs

#print axioms r2r_guarantee
