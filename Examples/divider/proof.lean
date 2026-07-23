import LeanModels.Spice.Surface

namespace Examples.divider.proof

open LeanModels.Spice

load_netlist divider from "Examples/divider/divider.json"

private def dividerFlat : FlatNetlist :=
  { elements := #[
      ⟨.vsource, ⟨12, 12⟩, "v1", "in", "0", 5⟩,
      ⟨.resistor, ⟨13, 13⟩, "r1", "in", "out", 1000⟩,
      ⟨.resistor, ⟨14, 14⟩, "r2", "out", "0", 2000⟩] }

private def dividerSolution : Assignment :=
  { volt := fun node => if node == "in" then 5 else if node == "out" then 10 / 3 else 0
    cur := fun name => if name == "v1" then -1 / 600 else 0 }

private theorem divider_flatten : flatten divider = .ok dividerFlat := by
  rfl

/-- Every DC state satisfying the extracted divider has the exact output
voltage `10/3`. -/
theorem divider_out : divider ⊨dc { v, _i => v "out" = 10 / 3 } := by
  intro assignment h
  unfold SatisfiesNetlist at h
  rw [divider_flatten] at h
  simp [Satisfies, dividerFlat, FlatNetlist.nodes, kclSum, currentInto,
    deviceLawHolds] at h
  grind

/-- The extracted divider has one operating point on all supported voltages
and branch currents. -/
theorem divider_wellposed : WellPosed divider := by
  refine ⟨dividerFlat, divider_flatten, dividerSolution, ?_, ?_⟩
  · simp [Satisfies, dividerFlat, dividerSolution, FlatNetlist.nodes,
      kclSum, currentInto, deviceLawHolds]
    grind
  · intro other h
    simp [Satisfies, dividerFlat, FlatNetlist.nodes, kclSum, currentInto,
      deviceLawHolds] at h
    simp [SupportEq, dividerFlat, dividerSolution, FlatNetlist.nodes,
      FlatNetlist.branchNames]
    grind

end Examples.divider.proof
