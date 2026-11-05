import LeanModels.Refine.Commit

/-!
# A latency-parametric memory/bus contract

`Commit.Input.memory` is the architectural, always-ready memory view.  A
clocked core instead issues memory requests and may receive a response after
an arbitrary finite number of cycles.  This file gives the refinement bridge
for that boundary without changing the ISA memory semantics: request service
uses the existing `Rv.loadVal` and `Rv.storeVal`, and completed requests are
reported as the existing `MemoryEffect` observations.

The contract is deliberately small and explicit.  Requests are accepted in
FIFO order, with at most one request outstanding; `latency : Nat → Nat` is an
oracle giving the number of bubble cycles before each response.  The theorem
quantifies over every oracle, so it does not choose a wait-state schedule.
Out-of-order completion and multiple outstanding requests belong to the ROB
and packet layers, where commit order is already an explicit proof
obligation.  This bridge only removes timing bubbles from an in-order memory
channel while preserving read-after-write behavior and the exact byte-level
memory update.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## Requests and exact service -/

/-- A data-memory request at the core/bus boundary.  The signed bit is part of
the request because it affects the value returned by a byte or halfword load;
stores retain the full register value and let `storeVal` select the bytes. -/
inductive BusRequest where
  | read (address : Word) (width : MemW) (signed : Bool)
  | write (address : Word) (width : MemW) (data : Word)
  deriving DecidableEq, Repr

/-- The architectural request shape carried by `Rv.StepEffects`. -/
def BusRequest.archEffect : BusRequest → Rv.MemEffect
  | .read address width _ => .read address width
  | .write address width data => .write address width data

/-- Service one request against the exact byte-addressed ISA memory. -/
def serviceBusRequest (memory : Memory) (request : BusRequest) :
    Memory × MemoryEffect :=
  match request with
  | .read address width signed =>
      (memory, .read address width (loadVal memory width signed address))
  | .write address width data =>
      (storeVal memory width address data, .write address width data)

/-! ## A finite timed bus trace -/

/-- A finite sequence of request/latency pairs is the explicit timing oracle.
The request order is the acceptance order; the natural number is the number
of response bubbles before that request completes. -/
abbrev TimedRequest := BusRequest × Nat

/-- Remove timing bubbles from a bus observation trace. -/
def completed {α : Type} : List (Option α) → List α
  | [] => []
  | none :: rest => completed rest
  | some value :: rest => value :: completed rest

@[simp] theorem completed_append {α : Type} (first second : List (Option α)) :
    completed (first ++ second) = completed first ++ completed second := by
  induction first with
  | nil => rfl
  | cons entry first ih =>
      cases entry <;> simp [completed, ih]

@[simp] theorem completed_delay (delay : Nat) (value : α)
    (rest : List (Option α)) :
    completed (List.replicate delay none ++ some value :: rest) =
      value :: completed rest := by
  induction delay with
  | zero => rfl
  | succ delay ih =>
      simp only [List.replicate_succ, List.cons_append, completed]
      exact ih

def directRun (memory : Memory) : List BusRequest →
    Memory × List MemoryEffect
  | [] => (memory, [])
  | request :: rest =>
      let (memory', effect) := serviceBusRequest memory request
      let (finalMemory, effects) := directRun memory' rest
      (finalMemory, effect :: effects)

/-- Execute a timed, FIFO bus.  A request is serviced when its response is
emitted; the recursive call then accepts the next request. -/
def runBus (memory : Memory) : List TimedRequest →
    Memory × List (Option MemoryEffect)
  | [] => (memory, [])
  | (request, delay) :: rest =>
      let (memory', effect) := serviceBusRequest memory request
      let (finalMemory, cycles) := runBus memory' rest
      (finalMemory, List.replicate delay none ++ some effect :: cycles)

/-! ## Every latency schedule has the same architectural projection -/

theorem runBus_projection (memory : Memory) (scheduled : List TimedRequest) :
    (runBus memory scheduled).1 =
        (directRun memory (scheduled.map Prod.fst)).1 ∧
      completed (runBus memory scheduled).2 =
        (directRun memory (scheduled.map Prod.fst)).2 := by
  induction scheduled generalizing memory with
  | nil =>
      simp [runBus, directRun, completed]
  | cons pair rest ih =>
      rcases pair with ⟨request, delay⟩
      simp only [runBus, directRun, List.map]
      let serviced := serviceBusRequest memory request
      have htail := ih (memory := serviced.1)
      simp only [serviced] at htail ⊢
      rcases htail with ⟨hMemory, hEffects⟩
      constructor
      · exact hMemory
      · rw [completed_delay]
        exact congrArg (fun effects => (serviceBusRequest memory request).2 :: effects)
          hEffects

/-! ## Adjacent timed windows -/

/-- A timed run composes by threading the final memory from its first window
into the second.  The response list retains the two windows' cycle order. -/
theorem runBus_append (memory : Memory) (first second : List TimedRequest) :
    (runBus memory (first ++ second)).1 =
        (runBus (runBus memory first).1 second).1 ∧
      (runBus memory (first ++ second)).2 =
        (runBus memory first).2 ++
          (runBus (runBus memory first).1 second).2 := by
  induction first generalizing memory with
  | nil => simp [runBus]
  | cons pair first ih =>
      rcases pair with ⟨request, delay⟩
      simp only [runBus, List.cons_append]
      let serviced := serviceBusRequest memory request
      have htail := ih (memory := serviced.1)
      simp only [serviced] at htail ⊢
      rcases htail with ⟨hMemory, hCycles⟩
      constructor
      · exact hMemory
      · rw [List.append_assoc]
        exact congrArg (fun cycles => List.replicate delay none ++
            some (serviceBusRequest memory request).2 :: cycles) hCycles

theorem completed_runBus_append (memory : Memory)
    (first second : List TimedRequest) :
    completed (runBus memory (first ++ second)).2 =
      completed (runBus memory first).2 ++
        completed (runBus (runBus memory first).1 second).2 := by
  have hrun := runBus_append memory first second
  rw [hrun.2]
  simp only [completed_append]

/-! ## A function-valued latency oracle -/

/-- Timing is supplied by the environment.  Every `Nat → Nat` is an allowed
finite-latency oracle; no convenient fixed delay is built into the contract. -/
abbrev LatencyOracle := Nat → Nat

def scheduleWith (latency : LatencyOracle) : List BusRequest → List TimedRequest
  | [] => []
  | request :: rest =>
      (request, latency 0) :: scheduleWith (fun index => latency (index + 1)) rest

/-- Shift a latency oracle to the index immediately after a finite window. -/
def latencyShift (latency : LatencyOracle) (offset : Nat) : LatencyOracle :=
  fun index => latency (index + offset)

/-- Scheduling commutes with splitting a request stream.  The second window
uses the same oracle at indices after the first window; no concrete delay
pattern is selected. -/
theorem scheduleWith_append (latency : LatencyOracle)
    (first second : List BusRequest) :
    scheduleWith latency (first ++ second) =
      scheduleWith latency first ++
        scheduleWith (latencyShift latency first.length) second := by
  induction first generalizing latency with
  | nil =>
      have hshift : latencyShift latency 0 = latency := by
        funext index
        simp [latencyShift]
      simp only [List.nil_append, List.length_nil]
      rw [hshift]
      simp [scheduleWith]
  | cons request first ih =>
      simp only [List.cons_append, scheduleWith]
      rw [ih (latency := fun index => latency (index + 1))]
      have hshift :
          latencyShift (fun index => latency (index + 1)) first.length =
            latencyShift latency (List.length (request :: first)) := by
        funext index
        simp [latencyShift, List.length_cons, Nat.add_assoc]
      rw [hshift]

@[simp] theorem scheduleWith_requests (latency : LatencyOracle)
    (requests : List BusRequest) :
    (scheduleWith latency requests).map Prod.fst = requests := by
  induction requests generalizing latency with
  | nil => rfl
  | cons request rest ih =>
      simp only [scheduleWith, List.map]
      rw [ih]

/-- Timing erasure is sound for every latency oracle: the final memory and
the completed memory-effect stream are exactly the direct always-ready run. -/
theorem runBus_oracle_projection (memory : Memory) (latency : LatencyOracle)
    (requests : List BusRequest) :
    (runBus memory (scheduleWith latency requests)).1 =
        (directRun memory requests).1 ∧
      completed (runBus memory (scheduleWith latency requests)).2 =
        (directRun memory requests).2 := by
  have h := runBus_projection memory (scheduleWith latency requests)
  simpa using h

end LeanModels.Refine

#print axioms LeanModels.Refine.runBus_projection
#print axioms LeanModels.Refine.completed_append
#print axioms LeanModels.Refine.runBus_append
#print axioms LeanModels.Refine.completed_runBus_append
#print axioms LeanModels.Refine.scheduleWith_append
#print axioms LeanModels.Refine.runBus_oracle_projection
