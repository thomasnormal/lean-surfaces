import LeanModels.Spice.Mos1

/-!
# Width-parametric addition from half-adder contracts

Bits are least-significant first. A full-adder stage is built from three
half-adders: the third combines the two mutually-exclusive carry terms, so no
unproved OR primitive is required. `RippleAdderOf` composes that stage for an
arbitrary list width.
-/

namespace LeanModels.Spice

abbrev HalfAdderRelation :=
  Bool → Bool → Bool → Bool → Prop

/-- A full adder assembled exclusively from three instances of `halfAdder`.
The final half-adder's carry output is unused because the two carry terms are
mutually exclusive for a correct half-adder. -/
def FullAdderOf (halfAdder : HalfAdderRelation)
    (left right carryIn sum carryOut : Bool) : Prop :=
  ∃ propagate generated propagatedCarry unused,
    halfAdder left right propagate generated ∧
    halfAdder propagate carryIn sum propagatedCarry ∧
    halfAdder generated propagatedCarry carryOut unused

/-- A least-significant-bit-first ripple composition. Mismatched widths are
false by definition. -/
def RippleAdderOf (halfAdder : HalfAdderRelation) :
    List Bool → List Bool → Bool → List Bool → Bool → Prop
  | [], [], carryIn, [], carryOut => carryOut = carryIn
  | left :: lefts, right :: rights, carryIn, sum :: sums, carryOut =>
      ∃ nextCarry,
        FullAdderOf halfAdder left right carryIn sum nextCarry ∧
        RippleAdderOf halfAdder lefts rights nextCarry sums carryOut
  | _, _, _, _, _ => False

def bitValue : Bool → Nat
  | false => 0
  | true => 1

/-- Natural-number value of a least-significant-bit-first word. -/
def bitsValue : List Bool → Nat
  | [] => 0
  | bit :: bits => bitValue bit + 2 * bitsValue bits

theorem fullAdderOf_behavior
    {left right carryIn sum carryOut : Bool}
    (hfull :
      FullAdderOf HalfAdderBehavior left right carryIn sum carryOut) :
    bitValue sum + 2 * bitValue carryOut =
      bitValue left + bitValue right + bitValue carryIn := by
  rcases hfull with
    ⟨propagate, generated, propagatedCarry, unused,
      hfirst, hsecond, hthird⟩
  rcases left with _ | _ <;> rcases right with _ | _ <;>
    rcases carryIn with _ | _ <;> rcases propagate with _ | _ <;>
    rcases generated with _ | _ <;> rcases propagatedCarry with _ | _ <;>
    rcases sum with _ | _ <;> rcases carryOut with _ | _ <;>
    simp [HalfAdderBehavior, bitValue] at hfirst hsecond hthird ⊢

/-- The arithmetic theorem for every width. -/
theorem rippleAdderOf_behavior
    {left right sum : List Bool} {carryIn carryOut : Bool}
    (hripple :
      RippleAdderOf HalfAdderBehavior left right carryIn sum carryOut) :
    bitsValue sum + 2 ^ left.length * bitValue carryOut =
      bitsValue left + bitsValue right + bitValue carryIn := by
  induction left generalizing right carryIn sum with
  | nil =>
      cases right <;> cases sum <;>
        simp [RippleAdderOf, bitsValue] at hripple ⊢
      subst carryOut
      rfl
  | cons left lefts ih =>
      cases right with
      | nil => simp [RippleAdderOf] at hripple
      | cons right rights =>
          cases sum with
          | nil => simp [RippleAdderOf] at hripple
          | cons sum sums =>
              rcases hripple with ⟨nextCarry, hfull, htail⟩
              have hhead := fullAdderOf_behavior hfull
              have hrest := ih htail
              rcases nextCarry with _ | _ <;> rcases carryOut with _ | _
              all_goals
                simp [bitsValue, bitValue, pow_succ] at hhead hrest ⊢
                all_goals
                  omega

theorem fullAdderOf_mono
    {source target : HalfAdderRelation}
    (hrefines : ∀ left right sum carry,
      source left right sum carry → target left right sum carry)
    {left right carryIn sum carryOut : Bool}
    (hfull : FullAdderOf source left right carryIn sum carryOut) :
    FullAdderOf target left right carryIn sum carryOut := by
  rcases hfull with
    ⟨propagate, generated, propagatedCarry, unused,
      hfirst, hsecond, hthird⟩
  exact ⟨propagate, generated, propagatedCarry, unused,
    hrefines _ _ _ _ hfirst,
    hrefines _ _ _ _ hsecond,
    hrefines _ _ _ _ hthird⟩

/-- Contract refinement is preserved by every-width ripple composition. -/
theorem rippleAdderOf_mono
    {source target : HalfAdderRelation}
    (hrefines : ∀ left right sum carry,
      source left right sum carry → target left right sum carry)
    {left right sum : List Bool} {carryIn carryOut : Bool}
    (hripple : RippleAdderOf source left right carryIn sum carryOut) :
    RippleAdderOf target left right carryIn sum carryOut := by
  induction left generalizing right carryIn sum with
  | nil =>
      cases right with
      | nil =>
          cases sum with
          | nil => simpa [RippleAdderOf] using hripple
          | cons _ _ => simp [RippleAdderOf] at hripple
      | cons _ _ => simp [RippleAdderOf] at hripple
  | cons left lefts ih =>
      cases right with
      | nil => simp [RippleAdderOf] at hripple
      | cons right rights =>
          cases sum with
          | nil => simp [RippleAdderOf] at hripple
          | cons sum sums =>
              rcases hripple with ⟨nextCarry, hfull, htail⟩
              exact ⟨nextCarry, fullAdderOf_mono hrefines hfull, ih htail⟩

end LeanModels.Spice
