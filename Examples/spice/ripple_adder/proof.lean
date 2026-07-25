import Examples.spice.half_adder.spec
import LeanModels.Spice.RippleNetlist
import LeanModels.Circuit.Surface
import LeanModels.Spice.Mos1Surface

namespace Examples.spice.ripple_adder.proof

open LeanModels.Circuit.Spice LeanModels.Spice

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

load_circuit_source rippleAdderDeckSource from
  "Examples/spice/ripple_adder/ripple_adder.cir"

noncomputable abbrev physicalHalfAdderRelation : HalfAdderRelation :=
  Mos1HalfAdderObservation halfAdderMos1
    (mos_node! halfAdderMos1 "a") (mos_node! halfAdderMos1 "b")
    (mos_node! halfAdderMos1 "sum") (mos_node! halfAdderMos1 "carry")

/-- A compositional physical observation for every literal `half_adder` call
reached by expanding this deck through its `full_adder` hierarchy. -/
noncomputable def RippleDeckObservation
    (deck : SourceCircuit) (levels : String → Bool) : Prop :=
  embeddedHalfAdderShape? deck =
      standaloneHalfAdderShape? halfAdderDeck_source ∧
    match expandHalfAdderCalls deck with
    | .error _ => False
    | .ok calls =>
        HalfAdderCallsObserve physicalHalfAdderRelation levels calls

/-- The source deck contains exactly 50 of our full-adder calls, each of which
expands to the proved three-half-adder implementation. -/
theorem ripple_adder_literal_layout :
    expandHalfAdderCalls rippleAdderDeckSource =
      .ok (expectedRippleCalls 50) := by
  circuit_reduce

/-- The `half_adder` reached through the 50-bit deck contains exactly the
same 20 model-resolved transistors as the separately proved component. -/
theorem ripple_adder_half_adder_implementation :
    embeddedHalfAdderShape? rippleAdderDeckSource =
      standaloneHalfAdderShape? halfAdderDeck_source := by
  rfl

/-- The physical MOS1 observation of one copied half-adder refines to the
Boolean relation used by structural composition. -/
theorem physical_half_adder_refines
    {left right sum carry : Bool}
    (hobservation :
      physicalHalfAdderRelation left right sum carry) :
    HalfAdderBehavior left right sum carry :=
  half_adder_mos1_correct.observation_sound hobservation

/-- Realizability twin for `physical_half_adder_refines`: for every Boolean
input pair the physical MOS1 observation set is inhabited, so the refinement
hypothesis is satisfiable. -/
theorem physical_half_adder_refines_realizable (left right : Bool) :
    ∃ sum carry, physicalHalfAdderRelation left right sum carry :=
  ⟨Bool.xor left right, Bool.and left right,
    half_adder_mos1_observation_exists left right⟩

/-- Our literal `full_adder` subcircuit is built from three physical
half-adder observations and satisfies the one-bit addition equation. -/
theorem physical_full_adder_correct
    {left right carryIn sum carryOut : Bool}
    (hfull :
      FullAdderOf physicalHalfAdderRelation
        left right carryIn sum carryOut) :
    bitValue sum + 2 * bitValue carryOut =
      bitValue left + bitValue right + bitValue carryIn := by
  apply fullAdderOf_behavior
  exact fullAdderOf_mono
    (fun _ _ _ _ => physical_half_adder_refines) hfull

/-- Realizability twin for `physical_full_adder_correct`: three physical
half-adder observations assemble a full-adder stage for every input vector. -/
theorem physical_full_adder_correct_realizable (left right carryIn : Bool) :
    ∃ sum carryOut,
      FullAdderOf physicalHalfAdderRelation left right carryIn sum carryOut := by
  refine ⟨Bool.xor (Bool.xor left right) carryIn,
    Bool.xor (Bool.and left right) (Bool.and (Bool.xor left right) carryIn),
    Bool.xor left right, Bool.and left right,
    Bool.and (Bool.xor left right) carryIn,
    Bool.and (Bool.and left right) (Bool.and (Bool.xor left right) carryIn),
    ?_, ?_, ?_⟩
  · exact half_adder_mos1_observation_exists left right
  · exact half_adder_mos1_observation_exists (Bool.xor left right) carryIn
  · exact half_adder_mos1_observation_exists (Bool.and left right)
      (Bool.and (Bool.xor left right) carryIn)

/-- For every width, a ripple network composed from physical observations of
the proved MOS1 half-adder satisfies exact unsigned addition. -/
theorem ripple_adder_mos1_correct
    {left right sum : List Bool} {carryIn carryOut : Bool}
    (hripple :
      RippleAdderOf physicalHalfAdderRelation
        left right carryIn sum carryOut) :
    bitsValue sum + 2 ^ left.length * bitValue carryOut =
      bitsValue left + bitsValue right + bitValue carryIn := by
  apply rippleAdderOf_behavior
  exact rippleAdderOf_mono
    (fun _ _ _ _ => physical_half_adder_refines) hripple

/-- Realizability twin for `ripple_adder_mos1_correct`: at every width,
equal-length input words and any carry-in admit a complete ripple network of
physical MOS1 half-adder observations. -/
theorem ripple_adder_mos1_correct_realizable
    (left right : List Bool) (hlength : left.length = right.length)
    (carryIn : Bool) :
    ∃ sum carryOut,
      RippleAdderOf physicalHalfAdderRelation
        left right carryIn sum carryOut := by
  induction left generalizing right carryIn with
  | nil =>
      cases right with
      | nil => exact ⟨[], carryIn, rfl⟩
      | cons _ _ => simp at hlength
  | cons leftBit leftBits ih =>
      cases right with
      | nil => simp at hlength
      | cons rightBit rightBits =>
          obtain ⟨sumBit, nextCarry, hfull⟩ :=
            physical_full_adder_correct_realizable leftBit rightBit carryIn
          obtain ⟨sumBits, carryOut, htail⟩ :=
            ih rightBits (by simpa using hlength) nextCarry
          exact ⟨sumBit :: sumBits, carryOut, nextCarry, hfull, htail⟩

/-- Every compositional physical observation of the literal 50-bit SPICE
hierarchy satisfies exact unsigned addition. The premise ranges over its 150
actual half-adder calls, not over a separately asserted ripple relation. -/
theorem ripple_adder_fifty_bit
    (levels : String → Bool)
    (hphysical : RippleDeckObservation rippleAdderDeckSource levels) :
    bitsValue (indexedBitsFrom levels "sum" 0 50) +
        2 ^ 50 * bitValue (levels "cout") =
      bitsValue (indexedBitsFrom levels "a" 0 50) +
        bitsValue (indexedBitsFrom levels "b" 0 50) +
          bitValue (levels "cin") := by
  unfold RippleDeckObservation at hphysical
  rcases hphysical with ⟨_, hphysical⟩
  rw [ripple_adder_literal_layout] at hphysical
  have hripple :=
    expectedRippleCalls_observe physicalHalfAdderRelation levels 50 hphysical
  have hcorrect := ripple_adder_mos1_correct hripple
  simpa [rippleCarryName] using hcorrect

/-- Realizability twin for `ripple_adder_fifty_bit`: the compositional
physical observation set of the literal 50-bit deck is inhabited (witnessed
by the all-zero rail assignment), so the headline theorem is not vacuous. -/
theorem ripple_adder_fifty_bit_realizable :
    ∃ levels, RippleDeckObservation rippleAdderDeckSource levels := by
  refine ⟨fun _ => false, ?_, ?_⟩
  · exact ripple_adder_half_adder_implementation
  · rw [ripple_adder_literal_layout]
    intro call _hcall
    exact half_adder_mos1_observation_exists false false

end Examples.spice.ripple_adder.proof
