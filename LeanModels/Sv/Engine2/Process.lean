import Lean

/-!
# Engine 2 process identity and lifecycle

IEEE 1800-2023 clause 9.7 supplies the five process-class statuses. They are
not scheduler queue states: an unblocked ready continuation is not executing,
and deferred fork startup is not explicit process-control suspension.

Registration identity is independent of reusable scheduler storage. This
module supplies no slot conversion, allocator, wait transition, scheduling
oracle or implementation refinement. Fresh-key allocation, historical registry
retention, wait ownership and cancellation remain future invariants.
-/

namespace LeanModels.Sv.Engine2

universe frameLevel

structure ProcessKey where
  registration : Nat
  deriving DecidableEq, Repr

/-- Consumer admission metadata, not an IEEE source-process classification. -/
inductive BodyKind where
  | fixedCallback
  | resumeThunk
  deriving DecidableEq, Repr

inductive ProcessStatus where
  | finished
  | running
  | waiting
  | suspended
  | killed
  deriving DecidableEq, Repr

/-- Underlying continuation phase. Under explicit suspension this is parked
state, not actual execution or an effective wait registration. -/
inductive ProcessPhase where
  | registered
  | ready
  | executing
  | waiting
  | deferred
  deriving DecidableEq, Repr

/-- `ready` means unblocked in this semantic schema, not raw native PS_Ready.
The opaque frame must retain continuation and original wait information when
needed. It is not an automatic-storage or registration-attachment authority. -/
inductive ProcessState (Frame : Type frameLevel) where
  | live (frame : Frame) (phase : ProcessPhase) (explicitlySuspended : Bool)
  | finished
  | killed
  deriving Repr

namespace ProcessState

variable {Frame : Type frameLevel}

def status : ProcessState Frame → ProcessStatus
  | .finished => .finished
  | .killed => .killed
  | .live _ _ true => .suspended
  | .live _ .waiting false => .waiting
  | .live _ _ false => .running

def isTerminal : ProcessState Frame → Bool
  | .finished | .killed => true
  | .live _ _ _ => false

/-- Necessary readiness only; queue membership, region eligibility and global
control are additional future dispatch conditions. -/
def isReady : ProcessState Frame → Bool
  | .live _ .ready false => true
  | _ => false

def frame? : ProcessState Frame → Option Frame
  | .live frame _ _ => some frame
  | .finished | .killed => none

#guard (status (.live () .ready false)) == .running
#guard (status (.live () .waiting false)) == .waiting
#guard (status (.live () .waiting true)) == .suspended
#guard (status (.live () .deferred false)) == .running
#guard (status (.live () .deferred true)) == .suspended
#guard (status (.finished : ProcessState Unit)) == .finished
#guard (status (.killed : ProcessState Unit)) == .killed
#guard !isReady (.live () .executing false)
#guard !isReady (.live () .deferred false)
#guard !isReady (.live () .ready true)
#guard isReady (.live () .ready false)
#guard (frame? (.finished : ProcessState Unit)).isNone

theorem status_finished_iff (state : ProcessState Frame) :
    state.status = .finished ↔ state = .finished := by
  cases state with
  | live frame phase suspended => cases suspended <;> cases phase <;> simp [status]
  | finished => simp [status]
  | killed => simp [status]

theorem status_killed_iff (state : ProcessState Frame) :
    state.status = .killed ↔ state = .killed := by
  cases state with
  | live frame phase suspended => cases suspended <;> cases phase <;> simp [status]
  | finished => simp [status]
  | killed => simp [status]

theorem status_suspended_iff (state : ProcessState Frame) :
    state.status = .suspended ↔
      ∃ frame phase, state = .live frame phase true := by
  cases state with
  | live frame phase suspended => cases suspended <;> cases phase <;> simp [status]
  | finished => simp [status]
  | killed => simp [status]

theorem status_waiting_iff (state : ProcessState Frame) :
    state.status = .waiting ↔
      ∃ frame, state = .live frame .waiting false := by
  cases state with
  | live frame phase suspended => cases suspended <;> cases phase <;> simp [status]
  | finished => simp [status]
  | killed => simp [status]

theorem isReady_iff (state : ProcessState Frame) :
    state.isReady = true ↔ ∃ frame, state = .live frame .ready false := by
  cases state with
  | live frame phase suspended => cases suspended <;> cases phase <;> simp [isReady]
  | finished => simp [isReady]
  | killed => simp [isReady]

theorem ready_status_running (state : ProcessState Frame) (ready : state.isReady = true) :
    state.status = .running := by
  obtain ⟨frame, rfl⟩ := (isReady_iff state).mp ready
  rfl

theorem isTerminal_iff (state : ProcessState Frame) :
    state.isTerminal = true ↔ state = .finished ∨ state = .killed := by
  cases state <;> simp [isTerminal]

theorem frame_isSome_iff (state : ProcessState Frame) :
    state.frame?.isSome = true ↔ state.isTerminal = false := by
  cases state <;> simp [frame?, isTerminal]

theorem terminal_not_ready (state : ProcessState Frame) (terminal : state.isTerminal = true) :
    state.isReady = false := by
  rcases (isTerminal_iff state).mp terminal with rfl | rfl <;> rfl

end ProcessState

/-- Control eligibility is independent certified provenance, not inferred
from body kind. Original registration attachments remain a separate boundary. -/
structure ProcessRecord (Frame : Type frameLevel) where
  key : ProcessKey
  bodyKind : BodyKind
  controlAllowed : Bool
  state : ProcessState Frame
  deriving Repr

namespace ProcessRecord

variable {Frame : Type frameLevel}

/-- Data replacement, not an execution or process-control transition. -/
def withState (record : ProcessRecord Frame) (state : ProcessState Frame) : ProcessRecord Frame :=
  { record with state := state }

theorem withState_key (record : ProcessRecord Frame) (state : ProcessState Frame) :
    (record.withState state).key = record.key := rfl

theorem withState_bodyKind (record : ProcessRecord Frame) (state : ProcessState Frame) :
    (record.withState state).bodyKind = record.bodyKind := rfl

theorem withState_controlAllowed (record : ProcessRecord Frame) (state : ProcessState Frame) :
    (record.withState state).controlAllowed = record.controlAllowed := rfl

end ProcessRecord

theorem processKey_eq_iff (first second : ProcessKey) :
    first = second ↔ first.registration = second.registration := by
  cases first
  cases second
  simp only [ProcessKey.mk.injEq]

#print axioms ProcessState.status_finished_iff
#print axioms ProcessState.status_suspended_iff
#print axioms ProcessState.status_waiting_iff
#print axioms ProcessState.ready_status_running
#print axioms ProcessState.frame_isSome_iff
#print axioms ProcessRecord.withState_key
#print axioms processKey_eq_iff

end LeanModels.Sv.Engine2
