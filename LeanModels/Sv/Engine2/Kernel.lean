import LeanModels.Sv.Engine2.Completion
import LeanModels.Sv.Engine2.Control
import LeanModels.Sv.Engine2.Event
import LeanModels.Sv.Engine2.Fork
import LeanModels.Sv.Engine2.NamedEvent
import LeanModels.Sv.Engine2.Signal
import LeanModels.Sv.Engine2.Update

/-!
# Engine 2 aggregate kernel state

`KernelState` is the first aggregate state vocabulary for Engine 2. It owns
semantic records for time/phase, process registrations, ordinary signals,
named events, current and future scheduled events, captured updates, forks,
process-control registrations, completion and output chunks. Every collection
is an explicit list so its order can be supplied by a later scheduler or
oracle; this module does not assign queue priority, perform publication,
advance time or execute a process body. No native address, allocator token or
duplicated authority is introduced by the aggregate.
-/

namespace LeanModels.Sv.Engine2

universe u

abbrev OutputChunks := List String

structure KernelState (Frame : Type u) where
  time : SimTime
  phase : Region
  processes : List (ProcessRecord Frame)
  signals : List SignalState
  namedEvents : List NamedEventState
  currentEvents : List ScheduledEvent
  futureEvents : List ScheduledEvent
  pendingUpdates : PendingUpdates
  forks : List ForkState
  controls : ControlState
  completion : CompletionState
  output : OutputChunks
  deriving Repr

namespace KernelState

variable {Frame : Type u}

def initial : KernelState Frame :=
  { time := .zero
    phase := .active
    processes := []
    signals := []
    namedEvents := []
    currentEvents := []
    futureEvents := []
    pendingUpdates := []
    forks := []
    controls := ControlState.initial
    completion := CompletionState.initial
    output := [] }

def processCount (state : KernelState Frame) : Nat :=
  state.processes.length

def signalCount (state : KernelState Frame) : Nat :=
  state.signals.length

def namedEventCount (state : KernelState Frame) : Nat :=
  state.namedEvents.length

def currentEventCount (state : KernelState Frame) : Nat :=
  state.currentEvents.length

def futureEventCount (state : KernelState Frame) : Nat :=
  state.futureEvents.length

def pendingUpdateCount (state : KernelState Frame) : Nat :=
  state.pendingUpdates.length

def forkCount (state : KernelState Frame) : Nat :=
  state.forks.length

def outputCount (state : KernelState Frame) : Nat :=
  state.output.length

def hasProcess (state : KernelState Frame) (key : ProcessKey) : Bool :=
  state.processes.any (fun process => process.key == key)

def hasSignal (state : KernelState Frame) (key : SignalKey) : Bool :=
  state.signals.any (fun signal => signal.key == key)

def hasNamedEvent (state : KernelState Frame) (key : NamedEventKey) : Bool :=
  state.namedEvents.any (fun event => event.key? == some key)

def hasFork (state : KernelState Frame) (key : ForkKey) : Bool :=
  state.forks.any (fun fork => fork.key == key)

theorem initial_time : (initial : KernelState Frame).time = .zero := rfl

theorem initial_phase : (initial : KernelState Frame).phase = .active := rfl

theorem initial_processes : (initial : KernelState Frame).processes = [] := rfl

theorem initial_signals : (initial : KernelState Frame).signals = [] := rfl

theorem initial_namedEvents : (initial : KernelState Frame).namedEvents = [] := rfl

theorem initial_currentEvents : (initial : KernelState Frame).currentEvents = [] := rfl

theorem initial_futureEvents : (initial : KernelState Frame).futureEvents = [] := rfl

theorem initial_pendingUpdates :
    (initial : KernelState Frame).pendingUpdates = [] := rfl

theorem initial_forks : (initial : KernelState Frame).forks = [] := rfl

theorem initial_controls :
    (initial : KernelState Frame).controls = ControlState.initial := rfl

theorem initial_completion :
    (initial : KernelState Frame).completion = CompletionState.initial := rfl

theorem initial_output : (initial : KernelState Frame).output = [] := rfl

theorem hasProcess_head (state : KernelState Frame)
    (process : ProcessRecord Frame) :
    ({ state with processes := process :: state.processes }).hasProcess process.key = true := by
  simp [hasProcess]

theorem hasSignal_head (state : KernelState Frame) (signal : SignalState) :
    ({ state with signals := signal :: state.signals }).hasSignal signal.key = true := by
  simp [hasSignal]

theorem hasNamedEvent_resolved_head (state : KernelState Frame)
    (key : NamedEventKey) :
    ({ state with namedEvents := NamedEventState.initial key :: state.namedEvents }).hasNamedEvent
      key = true := by
  simp [hasNamedEvent, NamedEventState.initial, NamedEventState.key?]

theorem hasFork_head (state : KernelState Frame) (fork : ForkState) :
    ({ state with forks := fork :: state.forks }).hasFork fork.key = true := by
  simp [hasFork]

end KernelState

#guard (KernelState.initial : KernelState Unit).time == .zero
#guard (KernelState.initial : KernelState Unit).phase == .active
#guard !(KernelState.initial : KernelState Unit).hasProcess ⟨0⟩
#guard !(KernelState.initial : KernelState Unit).hasSignal ⟨0⟩
#guard !(KernelState.initial : KernelState Unit).hasNamedEvent ⟨0⟩
#guard !(KernelState.initial : KernelState Unit).hasFork ⟨0⟩
#guard (KernelState.initial : KernelState Unit).processCount == 0
#guard (KernelState.initial : KernelState Unit).currentEventCount == 0
#guard (KernelState.initial : KernelState Unit).pendingUpdateCount == 0
#guard (KernelState.initial : KernelState Unit).outputCount == 0

#print axioms KernelState.hasProcess_head
#print axioms KernelState.hasSignal_head
#print axioms KernelState.hasNamedEvent_resolved_head
#print axioms KernelState.hasFork_head

end LeanModels.Sv.Engine2
