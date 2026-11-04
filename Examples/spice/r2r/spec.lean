import LeanModels.Python.Surface
import Examples.spice.r2r.proof

open LeanModels.Circuit

load_circuit r2rDeck from "Examples/spice/r2r/r2r.cir"

#circuit_check r2rDeck dc shows "out" = (25 / 8 : Rat)

/-- The source-backed R-2R component satisfies its exact transfer relation
for every four-bit environment drive vector. -/
theorem r2r_guarantee (bits : Fin 4 → Bool)
    (assignment : RealDCAssignment)
    (h : RealDCSatisfies r2rDeck
      (Examples.spice.r2r.proof.r2rWorld bits) assignment) :
    assignment.voltage Examples.spice.r2r.proof.outputNode =
      5 * Examples.spice.r2r.proof.binVal bits / 16 := by proofs

theorem r2r_realizable (bits : Fin 4 → Bool) :
    ∃ assignment, RealDCSatisfies r2rDeck
      (Examples.spice.r2r.proof.r2rWorld bits) assignment := by proofs

#print axioms r2r_guarantee
#print axioms r2r_realizable
