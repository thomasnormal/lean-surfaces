/-!
# Engine 2 completion state

`CompletionState` keeps the kernel's completion authority separate from
process termination. Initialization and current-slot draining are explicit
facts; an explicit finish request is a sticky optional status. Natural
completion is derived from an exhausted queue view outside a drain, so a
sensitized process may remain registered while the kernel is finished. This
module defines the state observations and first-request retention only; queue
draining, time advancement and reopening by publication are later rules.
-/

namespace LeanModels.Sv.Engine2

structure CompletionState where
  initialized : Bool
  draining : Bool
  explicitStatus : Option Int
  deriving DecidableEq, Repr

namespace CompletionState

def initial : CompletionState :=
  ⟨false, false, none⟩

def start (state : CompletionState) : CompletionState :=
  { state with initialized := true }

def beginDrain (state : CompletionState) : CompletionState :=
  { state with draining := true }

def endDrain (state : CompletionState) : CompletionState :=
  { state with draining := false }

def requestFinish (state : CompletionState) (status : Int) : CompletionState :=
  match state.explicitStatus with
  | some _ => state
  | none => { state with explicitStatus := some status }

def finishRequested (state : CompletionState) : Bool :=
  state.explicitStatus.isSome

def finishStatus (state : CompletionState) : Int :=
  state.explicitStatus.getD 0

/-- Queue exhaustion is supplied by the scheduler; it is not inferred from
process termination or from the registration table. -/
def naturallyFinished (state : CompletionState) (queuesEmpty : Bool) : Bool :=
  state.initialized && !state.draining && queuesEmpty && !state.finishRequested

def finished (state : CompletionState) (queuesEmpty : Bool) : Bool :=
  state.finishRequested || state.naturallyFinished queuesEmpty

theorem initial_not_initialized : initial.initialized = false := rfl

theorem initial_not_draining : initial.draining = false := rfl

theorem initial_not_requested : initial.finishRequested = false := by
  rfl

theorem start_initialized (state : CompletionState) :
    (start state).initialized = true := rfl

theorem beginDrain_draining (state : CompletionState) :
    (beginDrain state).draining = true := rfl

theorem endDrain_not_draining (state : CompletionState) :
    (endDrain state).draining = false := rfl

theorem requestFinish_first (state : CompletionState) (status : Int)
    (notRequested : state.explicitStatus = none) :
    (requestFinish state status).explicitStatus = some status := by
  simp [requestFinish, notRequested]

theorem requestFinish_retains (state : CompletionState) (status : Int)
    (requested : state.explicitStatus.isSome = true) :
    requestFinish state status = state := by
  cases value : state.explicitStatus with
  | none => simp [value] at requested
  | some prior => simp [requestFinish, value]

theorem requestFinish_sticky (state : CompletionState) (first second : Int) :
    (requestFinish (requestFinish state first) second).explicitStatus =
      (requestFinish state first).explicitStatus := by
  cases value : state.explicitStatus with
  | none => simp [requestFinish, value]
  | some prior => simp [requestFinish, value]

theorem naturallyFinished_requires_initialized (state : CompletionState)
    (queuesEmpty : Bool) (natural : state.naturallyFinished queuesEmpty = true) :
    state.initialized = true := by
  simp [naturallyFinished] at natural
  exact natural.1.1.1

theorem naturallyFinished_status_zero (state : CompletionState) (queuesEmpty : Bool)
    (natural : state.naturallyFinished queuesEmpty = true) :
    state.finishStatus = 0 := by
  cases value : state.explicitStatus with
  | none => simp [finishStatus, value]
  | some prior => simp [naturallyFinished, finishRequested, value] at natural

theorem finished_of_request (state : CompletionState) (queuesEmpty : Bool)
    (requested : state.finishRequested = true) :
    state.finished queuesEmpty = true := by
  simp [finished, requested]

theorem finished_of_natural (state : CompletionState) (queuesEmpty : Bool)
    (natural : state.naturallyFinished queuesEmpty = true) :
    state.finished queuesEmpty = true := by
  simp [finished, natural]

theorem not_naturallyFinished_during_drain (state : CompletionState)
    (queuesEmpty : Bool) (draining : state.draining = true) :
    state.naturallyFinished queuesEmpty = false := by
  simp [naturallyFinished, draining]

end CompletionState

#guard !CompletionState.initial.initialized
#guard !CompletionState.initial.draining
#guard !CompletionState.initial.finishRequested
#guard (CompletionState.start CompletionState.initial).initialized
#guard (CompletionState.beginDrain CompletionState.initial).draining
#guard !(CompletionState.endDrain (CompletionState.beginDrain CompletionState.initial)).draining
#guard (CompletionState.requestFinish CompletionState.initial 7).finishStatus == 7
#guard (CompletionState.requestFinish
  (CompletionState.requestFinish CompletionState.initial 7) 9).finishStatus == 7
#guard (CompletionState.start CompletionState.initial).naturallyFinished true
#guard !(CompletionState.beginDrain (CompletionState.start CompletionState.initial)).naturallyFinished true

#print axioms CompletionState.requestFinish_first
#print axioms CompletionState.requestFinish_retains
#print axioms CompletionState.requestFinish_sticky
#print axioms CompletionState.naturallyFinished_status_zero
#print axioms CompletionState.finished_of_request
#print axioms CompletionState.finished_of_natural

end LeanModels.Sv.Engine2
