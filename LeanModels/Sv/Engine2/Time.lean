import Init.Data.UInt.Lemmas
import Lean.Elab.Tactic.Omega

/-!
# Engine 2 normalized simulation time

Natural femtoseconds model physical simulation time after source delays have
been normalized. IEEE 1800-2023 clauses 3.14 and 4.5 supply the physical units
and chronological slots; choosing femtoseconds does not fix a design's global
precision to one femtosecond. Source rounding, unknown/negative delay values,
and `$time` scaling remain lowering obligations, not arithmetic in this module.

The 64-bit adapter is a checked specification boundary. It does not assert
that the current C++ kernel rejects overflowing timestamp additions. No
calendar, region transition, execution oracle or implementation refinement is
introduced by this schema piece.
-/

namespace LeanModels.Sv.Engine2

structure SimTime where
  femtoseconds : Nat
  deriving DecidableEq, Repr

namespace SimTime

instance : LE SimTime := ⟨fun earlier later => earlier.femtoseconds ≤ later.femtoseconds⟩

instance : LT SimTime := ⟨fun earlier later => earlier.femtoseconds < later.femtoseconds⟩

instance (earlier later : SimTime) : Decidable (earlier ≤ later) :=
  inferInstanceAs (Decidable (earlier.femtoseconds ≤ later.femtoseconds))

instance (earlier later : SimTime) : Decidable (earlier < later) :=
  inferInstanceAs (Decidable (earlier.femtoseconds < later.femtoseconds))

def zero : SimTime := ⟨0⟩

/-- Relative delay in already-normalized, known femtoseconds. -/
def after (time : SimTime) (delayFs : Nat) : SimTime :=
  ⟨time.femtoseconds + delayFs⟩

/-- Decode the runtime's unsigned 64-bit femtosecond counter exactly. -/
def ofABI (value : UInt64) : SimTime := ⟨value.toNat⟩

/-- Encoding is defined only for values below the ABI's exclusive bound. -/
def toABI (time : SimTime) : Option UInt64 :=
  if time.femtoseconds < UInt64.size then
    some (UInt64.ofNat time.femtoseconds)
  else
    none

/-- Check the mathematical target, not merely the two addends. -/
def checkedAfter (time : SimTime) (delayFs : Nat) : Option UInt64 :=
  (time.after delayFs).toABI

#guard zero.after 0 == zero
#guard (zero.after 7).femtoseconds == 7
#guard (zero.after 7).after 5 == zero.after 12
#guard zero < zero.after 1
#guard !(zero.after 1 < zero)
#guard (SimTime.mk (UInt64.size - 1)).toABI == some (UInt64.ofNat (UInt64.size - 1))
#guard (SimTime.mk UInt64.size).toABI == none
#guard (SimTime.mk (UInt64.size - 1)).checkedAfter 0 ==
  some (UInt64.ofNat (UInt64.size - 1))
#guard (SimTime.mk (UInt64.size - 1)).checkedAfter 1 == none
#guard (SimTime.mk (UInt64.size + 1)).checkedAfter 0 == none

theorem after_zero (time : SimTime) : time.after 0 = time := by
  cases time
  rfl

theorem after_add (time : SimTime) (firstFs secondFs : Nat) :
    (time.after firstFs).after secondFs = time.after (firstFs + secondFs) := by
  simp only [after, Nat.add_assoc]

theorem le_after (time : SimTime) (delayFs : Nat) : time ≤ time.after delayFs := by
  change time.femtoseconds ≤ time.femtoseconds + delayFs
  omega

theorem after_eq_self_iff (time : SimTime) (delayFs : Nat) :
    time.after delayFs = time ↔ delayFs = 0 := by
  cases time
  simp [after]

theorem lt_after_iff (time : SimTime) (delayFs : Nat) :
    time < time.after delayFs ↔ 0 < delayFs := by
  change time.femtoseconds < time.femtoseconds + delayFs ↔ 0 < delayFs
  omega

theorem after_mono (earlier later : SimTime) (firstFs secondFs : Nat)
    (timeOrder : earlier ≤ later) (delayOrder : firstFs ≤ secondFs) :
    earlier.after firstFs ≤ later.after secondFs := by
  change earlier.femtoseconds ≤ later.femtoseconds at timeOrder
  change earlier.femtoseconds + firstFs ≤ later.femtoseconds + secondFs
  omega

theorem toABI_ofABI (value : UInt64) : (ofABI value).toABI = some value := by
  simp [toABI, ofABI, value.toNat_lt_size]

theorem ofABI_of_toABI (time : SimTime) (value : UInt64)
    (encoded : time.toABI = some value) : ofABI value = time := by
  unfold toABI at encoded
  split at encoded
  next fits =>
    have sameValue : UInt64.ofNat time.femtoseconds = value := Option.some.inj encoded
    subst value
    cases time
    simp only [ofABI, UInt64.toNat_ofNat_of_lt' fits]
  next => simp at encoded

theorem toABI_none_iff (time : SimTime) :
    time.toABI = none ↔ UInt64.size ≤ time.femtoseconds := by
  simp only [toABI]
  split <;> simp_all <;> omega

theorem toABI_some_iff (time : SimTime) (value : UInt64) :
    time.toABI = some value ↔ ofABI value = time := by
  constructor
  · exact ofABI_of_toABI time value
  · intro decoded
    rw [← decoded, toABI_ofABI]

theorem checkedAfter_none_iff (time : SimTime) (delayFs : Nat) :
    time.checkedAfter delayFs = none ↔
      UInt64.size ≤ time.femtoseconds + delayFs := by
  exact toABI_none_iff (time.after delayFs)

theorem checkedAfter_some_iff (time : SimTime) (delayFs : Nat) (value : UInt64) :
    time.checkedAfter delayFs = some value ↔
      value.toNat = time.femtoseconds + delayFs := by
  rw [checkedAfter, toABI_some_iff]
  simp only [ofABI, after, SimTime.mk.injEq]

#print axioms after_add
#print axioms lt_after_iff
#print axioms after_mono
#print axioms toABI_ofABI
#print axioms ofABI_of_toABI
#print axioms toABI_none_iff
#print axioms checkedAfter_some_iff

end SimTime
end LeanModels.Sv.Engine2
