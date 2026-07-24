import Examples.spice.ripple_adder.proof

open LeanModels.Spice

load_mos1 rippleAdderDeck from
  "Examples/spice/ripple_adder/ripple_adder.json"

#guard rippleAdderDeck.hasUnsupported == false
#guard rippleAdderDeck.toMos1 matches .ok _
#guard match flattenSwitch rippleAdderDeck with
  | .ok flat => flat.cards.size == 252
  | .error _ => false

theorem physical_half_adder_refines
    {left right sum carry : Bool}
    (hobservation :
      Mos1HalfAdderObservation halfAdderMos1
        (node! halfAdderMos1 "a") (node! halfAdderMos1 "b")
        (node! halfAdderMos1 "sum") (node! halfAdderMos1 "carry")
        left right sum carry) :
    HalfAdderBehavior left right sum carry := by proofs

/-- Every-width arithmetic correctness for a ripple composition of the
physically proved MOS1 half-adder. -/
theorem ripple_adder_mos1_correct
    {left right sum : List Bool} {carryIn carryOut : Bool}
    (hripple :
      RippleAdderOf
        (Mos1HalfAdderObservation halfAdderMos1
          (node! halfAdderMos1 "a") (node! halfAdderMos1 "b")
          (node! halfAdderMos1 "sum") (node! halfAdderMos1 "carry"))
        left right carryIn sum carryOut) :
    bitsValue sum + 2 ^ left.length * bitValue carryOut =
      bitsValue left + bitsValue right + bitValue carryIn := by proofs

theorem ripple_adder_four_bit
    {left right sum : List Bool} {carryIn carryOut : Bool}
    (hwidth : left.length = 4)
    (hripple :
      RippleAdderOf
        (Mos1HalfAdderObservation halfAdderMos1
          (node! halfAdderMos1 "a") (node! halfAdderMos1 "b")
          (node! halfAdderMos1 "sum") (node! halfAdderMos1 "carry"))
        left right carryIn sum carryOut) :
    bitsValue sum + 16 * bitValue carryOut =
      bitsValue left + bitsValue right + bitValue carryIn := by proofs

#print axioms physical_half_adder_refines
#print axioms ripple_adder_mos1_correct
#print axioms ripple_adder_four_bit
