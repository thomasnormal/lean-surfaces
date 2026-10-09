import LeanModels.Sv.Engine2.Event

/-!
# Engine 2 pending-update captures

A pending update is the captured result of evaluating an update command before
any later queue admission or publication rule runs. Signal updates retain the
signal target and four-state value together; named-event updates retain only
their named-event target. The common record preserves semantic identity, due
time, region and provenance. This file deliberately does not define enqueue,
NBA ordering, publication, cancellation or scheduler transitions.
-/

namespace LeanModels.Sv.Engine2

inductive PendingUpdateTarget where
  | signal (target : SignalKey) (value : LVec)
  | namedEvent (target : NamedEventKey)
  deriving DecidableEq, Repr

inductive PendingUpdateKind where
  | signal
  | namedOccurrence
  deriving DecidableEq, Repr

namespace PendingUpdateTarget

def kind : PendingUpdateTarget → PendingUpdateKind
  | .signal _ _ => .signal
  | .namedEvent _ => .namedOccurrence

def action : PendingUpdateTarget → EventAction
  | .signal target value => .update target value
  | .namedEvent target => .occurrence target

theorem kind_signal (target : SignalKey) (value : LVec) :
    (.signal target value : PendingUpdateTarget).kind = .signal := rfl

theorem kind_namedEvent (target : NamedEventKey) :
    (.namedEvent target : PendingUpdateTarget).kind = .namedOccurrence := rfl

theorem action_signal (target : SignalKey) (value : LVec) :
    (.signal target value : PendingUpdateTarget).action = .update target value := rfl

theorem action_namedEvent (target : NamedEventKey) :
    (.namedEvent target : PendingUpdateTarget).action = .occurrence target := rfl

theorem kind_cases (target : PendingUpdateTarget) :
    target.kind = .signal ∨ target.kind = .namedOccurrence := by
  cases target <;> simp [kind]

end PendingUpdateTarget

structure PendingUpdate where
  key : EventKey
  due : SimTime
  region : Region
  target : PendingUpdateTarget
  origin : EventOrigin
  deriving DecidableEq, Repr

/-- A collection of captured updates, with no implied admission or ordering policy. -/
abbrev PendingUpdates := List PendingUpdate

namespace PendingUpdate

def kind (update : PendingUpdate) : PendingUpdateKind := update.target.kind

def action (update : PendingUpdate) : EventAction := update.target.action

def signalTarget? (update : PendingUpdate) : Option (SignalKey × LVec) :=
  match update.target with
  | .signal target value => some (target, value)
  | .namedEvent _ => none

def namedEventTarget? (update : PendingUpdate) : Option NamedEventKey :=
  match update.target with
  | .signal _ _ => none
  | .namedEvent target => some target

theorem kind_signal (key : EventKey) (due : SimTime) (region : Region)
    (target : SignalKey) (value : LVec) (origin : EventOrigin) :
    (PendingUpdate.mk key due region (.signal target value) origin).kind = .signal := rfl

theorem kind_namedEvent (key : EventKey) (due : SimTime) (region : Region)
    (target : NamedEventKey) (origin : EventOrigin) :
    (PendingUpdate.mk key due region (.namedEvent target) origin).kind = .namedOccurrence := rfl

theorem action_signal (key : EventKey) (due : SimTime) (region : Region)
    (target : SignalKey) (value : LVec) (origin : EventOrigin) :
    (PendingUpdate.mk key due region (.signal target value) origin).action =
      .update target value := rfl

theorem action_namedEvent (key : EventKey) (due : SimTime) (region : Region)
    (target : NamedEventKey) (origin : EventOrigin) :
    (PendingUpdate.mk key due region (.namedEvent target) origin).action =
      .occurrence target := rfl

theorem kind_cases (update : PendingUpdate) :
    update.kind = .signal ∨ update.kind = .namedOccurrence := by
  exact update.target.kind_cases

theorem signalTarget_signal (key : EventKey) (due : SimTime) (region : Region)
    (target : SignalKey) (value : LVec) (origin : EventOrigin) :
    (PendingUpdate.mk key due region (.signal target value) origin).signalTarget? =
      some (target, value) := rfl

theorem namedEventTarget_namedEvent (key : EventKey) (due : SimTime) (region : Region)
    (target : NamedEventKey) (origin : EventOrigin) :
    (PendingUpdate.mk key due region (.namedEvent target) origin).namedEventTarget? =
      some target := rfl

theorem key_preserved (update : PendingUpdate) : update.key = update.key := rfl

theorem due_preserved (update : PendingUpdate) : update.due = update.due := rfl

theorem region_preserved (update : PendingUpdate) : update.region = update.region := rfl

theorem origin_preserved (update : PendingUpdate) : update.origin = update.origin := rfl

end PendingUpdate

#guard PendingUpdateTarget.kind (.signal ⟨0⟩ ⟨#[.l1]⟩) == .signal
#guard PendingUpdateTarget.kind (.namedEvent ⟨1⟩) == .namedOccurrence
#guard PendingUpdateTarget.action (.signal ⟨0⟩ ⟨#[.l1]⟩) == .update ⟨0⟩ ⟨#[.l1]⟩
#guard PendingUpdateTarget.action (.namedEvent ⟨1⟩) == .occurrence ⟨1⟩
#guard PendingUpdate.signalTarget?
  (PendingUpdate.mk ⟨0⟩ .zero .nba (.signal ⟨0⟩ ⟨#[.l1]⟩) (.process ⟨0⟩)) ==
    some (⟨0⟩, ⟨#[.l1]⟩)
#guard PendingUpdate.namedEventTarget?
  (PendingUpdate.mk ⟨1⟩ .zero .active (.namedEvent ⟨1⟩) (.external 0)) == some ⟨1⟩

#print axioms PendingUpdateTarget.kind_cases
#print axioms PendingUpdate.kind_cases
#print axioms PendingUpdate.signalTarget_signal
#print axioms PendingUpdate.namedEventTarget_namedEvent

end LeanModels.Sv.Engine2
