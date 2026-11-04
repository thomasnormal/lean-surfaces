import Examples.spice.ripple_adder.proof

open LeanModels.Circuit.Spice LeanModels.Spice

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

load_circuit_source rippleAdderDeckSource from
  "Examples/spice/ripple_adder/ripple_adder.cir"

abbrev physicalHalfAdderRelation :=
  Examples.spice.ripple_adder.proof.physicalHalfAdderRelation

abbrev RippleDeckObservation :=
  Examples.spice.ripple_adder.proof.RippleDeckObservation

#guard (expandHalfAdderCalls rippleAdderDeckSource).toOption.map List.length ==
  some 150

theorem ripple_adder_literal_layout :
    expandHalfAdderCalls rippleAdderDeckSource =
      .ok (expectedRippleCalls 50) := by proofs

theorem ripple_adder_half_adder_implementation :
    embeddedHalfAdderShape? rippleAdderDeckSource =
      standaloneHalfAdderShape? halfAdderDeck_source := by proofs

theorem physical_half_adder_refines
    {left right sum carry : Bool}
    (hobservation :
      physicalHalfAdderRelation left right sum carry) :
    HalfAdderBehavior left right sum carry := by proofs

/-- Realizability twin: the physical observation hypothesis of
`physical_half_adder_refines` is satisfiable for every input pair. -/
theorem physical_half_adder_refines_realizable (left right : Bool) :
    ∃ sum carry, physicalHalfAdderRelation left right sum carry := by proofs

/-- One full-adder stage, implemented by three copies of the physically
proved transistor-level half-adder. -/
theorem physical_full_adder_correct
    {left right carryIn sum carryOut : Bool}
    (hfull :
      FullAdderOf physicalHalfAdderRelation
        left right carryIn sum carryOut) :
    bitValue sum + 2 * bitValue carryOut =
      bitValue left + bitValue right + bitValue carryIn := by proofs

/-- Realizability twin: the `FullAdderOf` hypothesis of
`physical_full_adder_correct` is satisfiable for every input vector. -/
theorem physical_full_adder_correct_realizable (left right carryIn : Bool) :
    ∃ sum carryOut,
      FullAdderOf physicalHalfAdderRelation
        left right carryIn sum carryOut := by proofs

/-- Every-width arithmetic correctness for a ripple composition of the
physically proved MOS1 half-adder. -/
theorem ripple_adder_mos1_correct
    {left right sum : List Bool} {carryIn carryOut : Bool}
    (hripple :
      RippleAdderOf physicalHalfAdderRelation
        left right carryIn sum carryOut) :
    bitsValue sum + 2 ^ left.length * bitValue carryOut =
      bitsValue left + bitsValue right + bitValue carryIn := by proofs

/-- Realizability twin: the `RippleAdderOf` hypothesis of
`ripple_adder_mos1_correct` is satisfiable at every width. -/
theorem ripple_adder_mos1_correct_realizable
    (left right : List Bool) (hlength : left.length = right.length)
    (carryIn : Bool) :
    ∃ sum carryOut,
      RippleAdderOf physicalHalfAdderRelation
        left right carryIn sum carryOut := by proofs

/-- The literal 50-stage SPICE hierarchy, after expanding its own full-adder
subcircuit into the 150 proved half-adder calls. -/
theorem ripple_adder_fifty_bit
    (levels : String → Bool)
    (hphysical : RippleDeckObservation rippleAdderDeckSource levels) :
    bitsValue (indexedBitsFrom levels "sum" 0 50) +
        2 ^ 50 * bitValue (levels "cout") =
      bitsValue (indexedBitsFrom levels "a" 0 50) +
        bitsValue (indexedBitsFrom levels "b" 0 50) +
          bitValue (levels "cin") := by proofs

/-- Realizability twin: the compositional physical observation hypothesis of
`ripple_adder_fifty_bit` is satisfiable for the literal 50-bit deck. -/
theorem ripple_adder_fifty_bit_realizable :
    ∃ levels, RippleDeckObservation rippleAdderDeckSource levels := by proofs

#print axioms ripple_adder_literal_layout
#print axioms ripple_adder_half_adder_implementation
#print axioms physical_half_adder_refines
#print axioms physical_half_adder_refines_realizable
#print axioms physical_full_adder_correct
#print axioms physical_full_adder_correct_realizable
#print axioms ripple_adder_mos1_correct
#print axioms ripple_adder_mos1_correct_realizable
#print axioms ripple_adder_fifty_bit
#print axioms ripple_adder_fifty_bit_realizable
