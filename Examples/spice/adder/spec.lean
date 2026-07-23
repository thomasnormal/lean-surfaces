import Examples.spice.adder.proof

open LeanModels.Spice
open Examples.spice.adder.proof (seriesAdder)

load_netlist adderDeck from "Examples/spice/adder/adder.json"

#spice_check adderDeck shows "out" = (5 : Rat)

theorem seriesAdder_correct (left right : Rat) :
    seriesAdder left right ⊨dc { v, _i => v "out" = left + right } := by proofs

theorem seriesAdder_wellposed (left right : Rat) :
    WellPosed (seriesAdder left right) := by proofs

theorem adder_is_instance : adderDeck = seriesAdder 2 3 := by proofs

theorem adder_out : adderDeck ⊨dc { v, _i => v "out" = 5 } := by proofs

#print axioms seriesAdder_correct
#print axioms seriesAdder_wellposed
#print axioms adder_out
