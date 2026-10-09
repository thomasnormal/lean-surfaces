import LeanModels.Sv.Engine2.Event

/-!
# Engine 2 named-event occurrence state

Named events are synchronization objects, not ordinary four-state values. A
state is either unresolved or resolved to a `NamedEventKey`; only a resolved
state may carry a last-occurrence time. The occurrence is valid for the
simulation time at which it was recorded, so `triggeredAt` is a pure current
time observation. No trigger, expiry, wait wakeup, alias resolution or queue
transition is defined here.
-/

namespace LeanModels.Sv.Engine2

inductive NamedEventState where
  | unresolved
  | resolved (key : NamedEventKey) (lastOccurrence : Option SimTime)
  deriving DecidableEq, Repr

namespace NamedEventState

def key? : NamedEventState → Option NamedEventKey
  | .unresolved => none
  | .resolved key _ => some key

def lastOccurrence? : NamedEventState → Option SimTime
  | .unresolved => none
  | .resolved _ occurrence => occurrence

def hasOccurrence : NamedEventState → Bool
  | .unresolved => false
  | .resolved _ none => false
  | .resolved _ (some _) => true

def triggeredAt : NamedEventState → SimTime → Bool
  | .unresolved, _ => false
  | .resolved _ occurrence, now => decide (occurrence = some now)

def initial (key : NamedEventKey) : NamedEventState := .resolved key none

def occurred (key : NamedEventKey) (time : SimTime) : NamedEventState :=
  .resolved key (some time)

theorem key_unresolved : NamedEventState.unresolved.key? = none := rfl

theorem key_resolved (key : NamedEventKey) (occurrence : Option SimTime) :
    (NamedEventState.resolved key occurrence).key? = some key := rfl

theorem lastOccurrence_unresolved :
    NamedEventState.unresolved.lastOccurrence? = none := rfl

theorem lastOccurrence_initial (key : NamedEventKey) :
    (initial key).lastOccurrence? = none := rfl

theorem lastOccurrence_occurred (key : NamedEventKey) (time : SimTime) :
    (occurred key time).lastOccurrence? = some time := rfl

theorem hasOccurrence_unresolved :
    NamedEventState.unresolved.hasOccurrence = false := rfl

theorem hasOccurrence_initial (key : NamedEventKey) :
    (initial key).hasOccurrence = false := rfl

theorem hasOccurrence_occurred (key : NamedEventKey) (time : SimTime) :
    (occurred key time).hasOccurrence = true := rfl

theorem triggeredAt_unresolved (time : SimTime) :
    NamedEventState.unresolved.triggeredAt time = false := rfl

theorem triggeredAt_initial (key : NamedEventKey) (time : SimTime) :
    (initial key).triggeredAt time = false := by
  rfl

theorem triggeredAt_occurred (key : NamedEventKey) (time : SimTime) :
    (occurred key time).triggeredAt time = true := by
  simp [occurred, triggeredAt]

theorem triggeredAt_expired (key : NamedEventKey) (occurredAt now : SimTime)
    (different : occurredAt ≠ now) :
    (occurred key occurredAt).triggeredAt now = false := by
  simp [occurred, triggeredAt, different]

theorem cases (state : NamedEventState) :
    state = .unresolved ∨ ∃ key occurrence, state = .resolved key occurrence := by
  cases state with
  | unresolved => exact Or.inl rfl
  | resolved key occurrence => exact Or.inr ⟨key, occurrence, rfl⟩

theorem resolved_has_key (state : NamedEventState)
    (resolved : state ≠ .unresolved) : state.key?.isSome = true := by
  cases state with
  | unresolved => contradiction
  | resolved key occurrence => simp [key?]

end NamedEventState

#guard NamedEventState.unresolved.key? == none
#guard (NamedEventState.initial ⟨0⟩).key? == some ⟨0⟩
#guard (NamedEventState.initial ⟨0⟩).lastOccurrence? == none
#guard !(NamedEventState.initial ⟨0⟩).hasOccurrence
#guard (NamedEventState.occurred ⟨0⟩ .zero).lastOccurrence? == some .zero
#guard (NamedEventState.occurred ⟨0⟩ .zero).hasOccurrence
#guard (NamedEventState.occurred ⟨0⟩ .zero).triggeredAt .zero
#guard !(NamedEventState.occurred ⟨0⟩ .zero).triggeredAt (SimTime.zero.after 1)

#print axioms NamedEventState.cases
#print axioms NamedEventState.triggeredAt_occurred
#print axioms NamedEventState.triggeredAt_expired
#print axioms NamedEventState.resolved_has_key

end LeanModels.Sv.Engine2
