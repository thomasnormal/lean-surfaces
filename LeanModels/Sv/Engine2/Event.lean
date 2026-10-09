import LeanModels.Sv.Basic
import LeanModels.Sv.Engine2.Process
import LeanModels.Sv.Engine2.Regions
import LeanModels.Sv.Engine2.Time
import LeanModels.Sv.Engine2.Wait

/-!
# Engine 2 scheduled-event vocabulary

An event is a semantic calendar entry, not a native queue node. Its identity,
time, region, action, origin and enqueue sequence are explicit data. Process
resumption, ordinary signal publication and named-event occurrence are
different actions even when they share a time and region. This module does not
define queue admission, ordering, cancellation, publication, or scheduler
transitions; those rules will consume this vocabulary later.

The sequence field records provenance supplied by a future scheduler or oracle;
it is not an assertion that independent events have a mandated total order.
-/

namespace LeanModels.Sv.Engine2

structure EventKey where
  registration : Nat
  deriving DecidableEq, Repr

inductive EventAction where
  | resume (wait : WaitIdentity)
  | update (signal : SignalKey) (value : LVec)
  | occurrence (event : NamedEventKey)
  deriving DecidableEq, Repr

inductive EventOrigin where
  | process (process : ProcessKey)
  | wait (wait : WaitIdentity)
  | external (source : Nat)
  deriving DecidableEq, Repr

inductive EventKind where
  | processResume
  | signalUpdate
  | namedOccurrence
  deriving DecidableEq, Repr

def EventAction.kind : EventAction → EventKind
  | .resume _ => .processResume
  | .update _ _ => .signalUpdate
  | .occurrence _ => .namedOccurrence

structure ScheduledEvent where
  key : EventKey
  time : SimTime
  region : Region
  action : EventAction
  origin : EventOrigin
  sequence : Nat
  deriving DecidableEq, Repr

namespace ScheduledEvent

def kind (event : ScheduledEvent) : EventKind := event.action.kind

def isProcessResume (event : ScheduledEvent) : Bool :=
  event.kind == .processResume

def isSignalUpdate (event : ScheduledEvent) : Bool :=
  event.kind == .signalUpdate

def isNamedOccurrence (event : ScheduledEvent) : Bool :=
  event.kind == .namedOccurrence

theorem kind_resume (key : EventKey) (time : SimTime) (region : Region)
    (wait : WaitIdentity) (origin : EventOrigin) (sequence : Nat) :
    (ScheduledEvent.mk key time region (.resume wait) origin sequence).kind =
      .processResume := rfl

theorem kind_update (key : EventKey) (time : SimTime) (region : Region)
    (signal : SignalKey) (value : LVec) (origin : EventOrigin) (sequence : Nat) :
    (ScheduledEvent.mk key time region (.update signal value) origin sequence).kind =
      .signalUpdate := rfl

theorem kind_occurrence (key : EventKey) (time : SimTime) (region : Region)
    (event : NamedEventKey) (origin : EventOrigin) (sequence : Nat) :
    (ScheduledEvent.mk key time region (.occurrence event) origin sequence).kind =
      .namedOccurrence := rfl

theorem kind_cases (event : ScheduledEvent) :
    event.kind = .processResume ∨ event.kind = .signalUpdate ∨
      event.kind = .namedOccurrence := by
  cases event with
  | mk key time region action origin sequence =>
    cases action <;> simp [kind, EventAction.kind]

theorem key_preserved (event : ScheduledEvent) : event.key = event.key := rfl

theorem time_preserved (event : ScheduledEvent) : event.time = event.time := rfl

theorem region_preserved (event : ScheduledEvent) : event.region = event.region := rfl

theorem sequence_preserved (event : ScheduledEvent) : event.sequence = event.sequence := rfl

end ScheduledEvent

#guard EventAction.kind (.resume (⟨⟨0⟩, ⟨⟨0⟩, 0⟩⟩)) == .processResume
#guard EventAction.kind (.update ⟨0⟩ ⟨#[.l1]⟩) == .signalUpdate
#guard EventAction.kind (.occurrence ⟨0⟩) == .namedOccurrence
#guard ScheduledEvent.isProcessResume
  (ScheduledEvent.mk ⟨0⟩ .zero .active
    (.resume (⟨⟨0⟩, ⟨⟨0⟩, 0⟩⟩)) (.wait (⟨⟨0⟩, ⟨⟨0⟩, 0⟩⟩)) 0)
#guard ScheduledEvent.isSignalUpdate
  (ScheduledEvent.mk ⟨1⟩ .zero .nba
    (.update ⟨0⟩ ⟨#[.l1]⟩) (.process ⟨0⟩) 1)
#guard ScheduledEvent.isNamedOccurrence
  (ScheduledEvent.mk ⟨2⟩ .zero .active
    (.occurrence ⟨0⟩) (.external 0) 2)

#print axioms ScheduledEvent.kind_cases
#print axioms ScheduledEvent.kind_resume
#print axioms ScheduledEvent.kind_update
#print axioms ScheduledEvent.kind_occurrence

end LeanModels.Sv.Engine2
