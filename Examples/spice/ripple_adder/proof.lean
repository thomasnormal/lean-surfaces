import Examples.spice.half_adder.spec
import LeanModels.Spice.Ripple
import LeanModels.Spice.Surface

namespace Examples.spice.ripple_adder.proof

open LeanModels.Spice

load_mos1 rippleAdderDeck from
  "Examples/spice/ripple_adder/ripple_adder.json"

/-- The physical MOS1 observation of one copied half-adder refines to the
Boolean relation used by structural composition. -/
theorem physical_half_adder_refines
    {left right sum carry : Bool}
    (hobservation :
      Mos1HalfAdderObservation halfAdderMos1
        (node! halfAdderMos1 "a") (node! halfAdderMos1 "b")
        (node! halfAdderMos1 "sum") (node! halfAdderMos1 "carry")
        left right sum carry) :
    HalfAdderBehavior left right sum carry :=
  half_adder_mos1_correct.observation_sound hobservation

/-- For every width, a ripple network composed from physical observations of
the proved MOS1 half-adder satisfies exact unsigned addition. -/
theorem ripple_adder_mos1_correct
    {left right sum : List Bool} {carryIn carryOut : Bool}
    (hripple :
      RippleAdderOf
        (Mos1HalfAdderObservation halfAdderMos1
          (node! halfAdderMos1 "a") (node! halfAdderMos1 "b")
          (node! halfAdderMos1 "sum") (node! halfAdderMos1 "carry"))
        left right carryIn sum carryOut) :
    bitsValue sum + 2 ^ left.length * bitValue carryOut =
      bitsValue left + bitsValue right + bitValue carryIn := by
  apply rippleAdderOf_behavior
  exact rippleAdderOf_mono
    (fun _ _ _ _ => physical_half_adder_refines) hripple

/-- Four-bit specialization of the width-parametric theorem. -/
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
      bitsValue left + bitsValue right + bitValue carryIn := by
  have hcorrect := ripple_adder_mos1_correct hripple
  simpa [hwidth] using hcorrect

end Examples.spice.ripple_adder.proof
