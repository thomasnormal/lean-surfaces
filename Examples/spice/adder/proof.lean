import LeanModels.Spice.Surface

namespace Examples.spice.adder.proof

open LeanModels.Spice

load_netlist adderDeck from "Examples/spice/adder/adder.json"

/-- Override one named element's value without changing any extracted
topology, names, nodes, source spans, or card ordering. -/
private def overrideElementValue (target : String) (value : Rat)
    (element : Element) : Element :=
  if element.name == target then { element with value } else element

private def overrideCardValue (target : String) (value : Rat) : Card → Card
  | .element element => .element (overrideElementValue target value element)
  | card => card

private def overrideNetlistValue (target : String) (value : Rat)
    (netlist : Netlist) : Netlist :=
  { netlist with cards := netlist.cards.map (overrideCardValue target value) }

private def overrideFlatValue (target : String) (value : Rat)
    (netlist : FlatNetlist) : FlatNetlist :=
  { elements := netlist.elements.map (overrideElementValue target value) }

/-- The extracted deck generalized only at its two source-value slots. The
circuit topology remains the literal AST loaded from `adder.cir`. -/
def seriesAdder (left right : Rat) : Netlist :=
  adderDeck
    |> overrideNetlistValue "vleft" left
    |> overrideNetlistValue "vright" right

private def seriesAdderFlat (left right : Rat) : FlatNetlist :=
  adderDeck_flat
    |> overrideFlatValue "vleft" left
    |> overrideFlatValue "vright" right

private theorem seriesAdder_flatten (left right : Rat) :
    flatten (seriesAdder left right) = .ok (seriesAdderFlat left right) := by
  simp [seriesAdder, seriesAdderFlat, overrideNetlistValue, overrideFlatValue,
    overrideCardValue, overrideElementValue, adderDeck, adderDeck_flat,
    flatten, flattenBudget, flattenCards, renameElement, renameNode,
    lookupRename, qualify]

/-- Stacking two ideal voltage sources adds their voltages exactly. -/
theorem seriesAdder_correct (left right : Rat) :
    seriesAdder left right ⊨dc { v, _i => v "out" = left + right } := by
  intro assignment h
  unfold SatisfiesNetlist at h
  rw [seriesAdder_flatten] at h
  simp [Satisfies, seriesAdderFlat, overrideFlatValue, overrideElementValue,
    adderDeck_flat, FlatNetlist.nodes, kclSum, currentInto,
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
  · simp [Satisfies, seriesAdderFlat, overrideFlatValue, overrideElementValue,
      adderDeck_flat, seriesAdderAssignment, FlatNetlist.nodes, kclSum,
      currentInto, deviceLawHolds]
  · intro other h
    simp [Satisfies, seriesAdderFlat, overrideFlatValue, overrideElementValue,
      adderDeck_flat, FlatNetlist.nodes, kclSum, currentInto,
      deviceLawHolds] at h
    simp [SupportEq, seriesAdderFlat, overrideFlatValue, overrideElementValue,
      adderDeck_flat, seriesAdderAssignment, FlatNetlist.nodes,
      FlatNetlist.branchNames]
    grind

/-- The checked-in netlist is the `2 + 3` instance of the symbolic family. -/
theorem adder_is_instance : adderDeck = seriesAdder 2 3 := by
  simp [seriesAdder, overrideNetlistValue, overrideCardValue,
    overrideElementValue, adderDeck]

theorem adder_out : adderDeck ⊨dc { v, _i => v "out" = 5 } := by
  spice_solve

end Examples.spice.adder.proof
