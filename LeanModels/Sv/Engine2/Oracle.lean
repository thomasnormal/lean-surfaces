import LeanModels.Sv.Engine2.Event

/-!
# Engine 2 scheduling oracle boundary

`SchedulingOracle` is the policy boundary for choosing among already-eligible
events. The transition relation supplies the eligible list and therefore owns
mandated region/phase filtering; the oracle may only select one member of that
list. A nonempty eligible list must produce a selection, while an empty list
may produce no event. Time advancement, region order, process statement order,
NBA ordering and event eligibility are not oracle choices here.
-/

namespace LeanModels.Sv.Engine2

abbrev EligibleEvents := List ScheduledEvent

structure SchedulingOracle where
  select : Nat → SimTime → Region → EligibleEvents → Option ScheduledEvent
  select_mem : ∀ (invocation : Nat) (time : SimTime) (region : Region)
    (eligible : EligibleEvents) (event : ScheduledEvent),
    select invocation time region eligible = some event → event ∈ eligible
  select_some : ∀ (invocation : Nat) (time : SimTime) (region : Region)
    (eligible : EligibleEvents), eligible ≠ [] → (select invocation time region eligible).isSome = true

namespace SchedulingOracle

def head : SchedulingOracle where
  select := fun _ _ _ eligible => eligible.head?
  select_mem := by
    intro invocation time region eligible event selected
    cases eligible with
    | nil => simp at selected
    | cons first rest =>
        simp at selected
        exact selected ▸ List.mem_cons_self
  select_some := by
    intro invocation time region eligible nonempty
    cases eligible with
    | nil => contradiction
    | cons first rest => simp

theorem select_mem_of (oracle : SchedulingOracle) (invocation : Nat)
    (time : SimTime) (region : Region) (eligible : EligibleEvents)
    (event : ScheduledEvent)
    (selected : oracle.select invocation time region eligible = some event) :
    event ∈ eligible := by
  exact oracle.select_mem invocation time region eligible event selected

theorem select_some_of (oracle : SchedulingOracle) (invocation : Nat)
    (time : SimTime) (region : Region) (eligible : EligibleEvents)
    (nonempty : eligible ≠ []) :
    (oracle.select invocation time region eligible).isSome = true := by
  exact oracle.select_some invocation time region eligible nonempty

theorem head_select_mem (invocation : Nat) (time : SimTime) (region : Region)
    (eligible : EligibleEvents) (event : ScheduledEvent)
    (selected : head.select invocation time region eligible = some event) :
    event ∈ eligible := by
  exact head.select_mem invocation time region eligible event selected

theorem head_select_some (invocation : Nat) (time : SimTime) (region : Region)
    (eligible : EligibleEvents) (nonempty : eligible ≠ []) :
    (head.select invocation time region eligible).isSome = true := by
  exact head.select_some invocation time region eligible nonempty

end SchedulingOracle

#guard (SchedulingOracle.head.select 0 .zero .active []).isNone
#guard (SchedulingOracle.head.select 0 .zero .active
  [ScheduledEvent.mk ⟨0⟩ .zero .active
    (.occurrence ⟨0⟩) (.external 0) 0]).isSome

#print axioms SchedulingOracle.select_mem_of
#print axioms SchedulingOracle.select_some_of
#print axioms SchedulingOracle.head_select_mem
#print axioms SchedulingOracle.head_select_some

end LeanModels.Sv.Engine2
