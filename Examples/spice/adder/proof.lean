import LeanModels.Spice.Surface

namespace Examples.spice.adder.proof

open LeanModels.Spice

load_netlist adderDeck from "Examples/spice/adder/adder.json"

/-- The extracted example generalized to arbitrary rational source values. -/
def seriesAdder (left right : Rat) : Netlist :=
  { title := "ideal series-source voltage adder"
    subckts := #[]
    cards := #[
      .element ⟨.vsource, ⟨12, 12⟩, "vleft", "mid", "0", left⟩,
      .element ⟨.vsource, ⟨13, 13⟩, "vright", "out", "mid", right⟩,
      .op ⟨14, 14⟩] }

private def seriesAdderFlat (left right : Rat) : FlatNetlist :=
  { elements := #[
      ⟨.vsource, ⟨12, 12⟩, "vleft", "mid", "0", left⟩,
      ⟨.vsource, ⟨13, 13⟩, "vright", "out", "mid", right⟩] }

private theorem seriesAdder_flatten (left right : Rat) :
    flatten (seriesAdder left right) = .ok (seriesAdderFlat left right) := by
  rfl

/-- Stacking two ideal voltage sources adds their voltages exactly. -/
theorem seriesAdder_correct (left right : Rat) :
    seriesAdder left right ⊨dc { v, _i => v "out" = left + right } := by
  intro assignment h
  unfold SatisfiesNetlist at h
  rw [seriesAdder_flatten] at h
  simp [Satisfies, seriesAdderFlat, FlatNetlist.nodes, kclSum, currentInto,
    deviceLawHolds] at h
  grind

private def seriesAdderAssignment (left right : Rat) : Assignment :=
  { volt := fun node =>
      if node == "mid" then left
      else if node == "out" then left + right
      else 0
    cur := fun _ => 0 }

/-- The symbolic adder has one DC operating point on every supported voltage
and branch current, for all rational inputs. -/
theorem seriesAdder_wellposed (left right : Rat) :
    WellPosed (seriesAdder left right) := by
  refine ⟨seriesAdderFlat left right, seriesAdder_flatten left right,
    seriesAdderAssignment left right, ?_, ?_⟩
  · simp [Satisfies, seriesAdderFlat, seriesAdderAssignment,
      FlatNetlist.nodes, kclSum, currentInto, deviceLawHolds]
  · intro other h
    simp [Satisfies, seriesAdderFlat, FlatNetlist.nodes, kclSum, currentInto,
      deviceLawHolds] at h
    simp [SupportEq, seriesAdderFlat, seriesAdderAssignment,
      FlatNetlist.nodes, FlatNetlist.branchNames]
    grind

/-- The checked-in netlist is the `2 + 3` instance of the symbolic family. -/
theorem adder_is_instance : adderDeck = seriesAdder 2 3 := by
  rfl

theorem adder_out : adderDeck ⊨dc { v, _i => v "out" = 5 } := by
  spice_solve

end Examples.spice.adder.proof
