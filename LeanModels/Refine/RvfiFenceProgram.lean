import LeanModels.Refine.RvfiRv32i
import LeanModels.Refine.Rv32iFence

/-!
# Symbolic RVFI programs made only of RV32I fence instructions

`FenceInstruction` retains the fetched word, semantic fence/fence.i kind, and decoder proof.
The folds below carry an arbitrary fence program through the stateful RV32I machine.  `FenceRvfiTrace` is the proof-facing
certificate for a packed RVFI stream: invalid rows are bubbles and every
retiring row supplies the indexed fence boundary for the next architectural
state.

This is the fence-family counterpart of `RvfiAddiProgram`.  It is deliberately a
program certificate rather than a core model; a loaded-core invariant still
has to establish the indexed `Rv32iBoundary` at each retiring cycle.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## A decoded fence program -/

/-! The semantic fence/fence.i shape retained by one decoded instruction. -/
structure FenceInstruction where
  word : Word
  kind : FenceKind
  decode : Fetched.decode (.word word) = some (.system kind.toSysOp)

/-- The architectural input associated with one fence instruction. -/
def fenceProgramInput (memory : Memory) (instruction : FenceInstruction) : Input :=
  { fetched := .word instruction.word, memory := memory, irq := 0 }

/-- The cycle/commit inputs for a fence program.  Fence instructions do not
mutate data memory, so every instruction sees the same threaded memory. -/
def fenceProgramInputs (memory : Memory) : List FenceInstruction → List Input
  | [] => []
  | instruction :: program =>
      fenceProgramInput memory instruction :: fenceProgramInputs memory program

/-- The architectural state after executing a fence program. -/
def fenceProgramState (state : ArchState) : List FenceInstruction → ArchState
  | [] => state
  | instruction :: program =>
      fenceProgramState
        (fenceNext state instruction.kind) program

/-- The exact retirement stream for a fence program. -/
def fenceProgramRetirements (memory : Memory) (state : ArchState) :
    List FenceInstruction → List Retirement
  | [] => []
  | instruction :: program =>
      fenceRetirement state (fenceProgramInput memory instruction) instruction.kind ::
        fenceProgramRetirements memory
          (fenceNext state instruction.kind) program

/-! ## Program-fold composition -/

/-- The input fold preserves list concatenation. -/
theorem fenceProgramInputs_append (memory : Memory)
    (first second : List FenceInstruction) :
    fenceProgramInputs memory (first ++ second) =
      fenceProgramInputs memory first ++ fenceProgramInputs memory second := by
  induction first with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, fenceProgramInputs, ih, List.cons_append]

/-- The architectural fence fold resumes from the state reached by its prefix. -/
theorem fenceProgramState_append (state : ArchState)
    (first second : List FenceInstruction) :
    fenceProgramState state (first ++ second) =
      fenceProgramState (fenceProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, fenceProgramState]
      exact ih (state :=
        fenceNext state instruction.kind)

/-- The retirement fold carries the same architectural prefix boundary as the
state fold. -/
theorem fenceProgramRetirements_append (memory : Memory) (state : ArchState)
    (first second : List FenceInstruction) :
    fenceProgramRetirements memory state (first ++ second) =
      fenceProgramRetirements memory state first ++
        fenceProgramRetirements memory (fenceProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, fenceProgramRetirements]
      rw [ih (state :=
        fenceNext state instruction.kind)]
      rfl

/-! ## Stateful ISA equations -/

/-- One decoded fence instruction drives the exact stateful ISA transition
with no memory update. -/
theorem rvMemoryMachineWith_fence_step
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (instruction : FenceInstruction) :
    (rvMemoryMachineWith profile).step
        { arch := state, memory := memory }
        (fenceProgramInput memory instruction) =
      ({ arch := fenceNext state instruction.kind, memory := memory },
        fenceRetirement state (fenceProgramInput memory instruction)
          instruction.kind) := by
  simp only [rvMemoryMachineWith, fenceProgramInput]
  rw [isaStepWith_fence profile state memory instruction.word instruction.kind
    instruction.decode]
  rfl

/-- Threading the stateful ISA machine through every fence instruction gives the
folded architectural state and unchanged memory. -/
theorem rvMemoryMachineWith_fence_program_state
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (program : List FenceInstruction) :
    machineStateAfter (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (fenceProgramInputs memory program) =
      { arch := fenceProgramState state program, memory := memory } := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [fenceProgramInputs, machineStateAfter]
      rw [rvMemoryMachineWith_fence_step profile state memory instruction]
      simpa [fenceProgramState] using
        (ih (state := fenceNext state instruction.kind))

/-- The same fence program has exactly the retirement stream prescribed by its
architectural fold. -/
theorem rvMemoryMachineWith_fence_program_trace
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (program : List FenceInstruction) :
    trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (fenceProgramInputs memory program) =
      fenceProgramRetirements memory state program := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [fenceProgramInputs, trace, fenceProgramRetirements]
      change
        ((rvMemoryMachineWith profile).step
            { arch := state, memory := memory }
            (fenceProgramInput memory instruction)).2 ::
          trace (rvMemoryMachineWith profile)
            ((rvMemoryMachineWith profile).step
              { arch := state, memory := memory }
              (fenceProgramInput memory instruction)).1
            (fenceProgramInputs memory program) = _
      rw [rvMemoryMachineWith_fence_step profile state memory instruction]
      simpa using
        (ih (state := fenceNext state instruction.kind))

/-- The stateful fence machine resumes at the exact memory-machine state after
the first program segment. -/
theorem rvMemoryMachineWith_fence_program_state_append
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (first second : List FenceInstruction) :
    machineStateAfter (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (fenceProgramInputs memory (first ++ second)) =
      machineStateAfter (rvMemoryMachineWith profile)
        (machineStateAfter (rvMemoryMachineWith profile)
          { arch := state, memory := memory }
          (fenceProgramInputs memory first))
        (fenceProgramInputs memory second) := by
  rw [fenceProgramInputs_append, machineStateAfter_append]

/-- The stateful fence retirement stream splits at the same first-segment
boundary as the architectural state. -/
theorem rvMemoryMachineWith_fence_program_trace_append
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (first second : List FenceInstruction) :
    trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (fenceProgramInputs memory (first ++ second)) =
      trace (rvMemoryMachineWith profile)
          { arch := state, memory := memory }
          (fenceProgramInputs memory first) ++
        trace (rvMemoryMachineWith profile)
          (machineStateAfter (rvMemoryMachineWith profile)
            { arch := state, memory := memory }
            (fenceProgramInputs memory first))
          (fenceProgramInputs memory second) := by
  rw [fenceProgramInputs_append, machineTrace_append]

/-! ## Raw RVFI certificate for an arbitrary fence program -/

/-- A raw RVFI stream whose retiring rows are exactly the supplied fence
program. -/
inductive FenceRvfiTrace (memory : Memory) :
    Nat → ArchState → List RvfiObservation → List FenceInstruction → Prop where
  | nil (start : Nat) (state : ArchState) :
      FenceRvfiTrace memory start state [] []
  | bubble {start : Nat} {state : ArchState}
      {observation : RvfiObservation} {observations : List RvfiObservation}
      {program : List FenceInstruction}
      (hvalid : observation.valid = false)
      (tail : FenceRvfiTrace memory start state observations program) :
      FenceRvfiTrace memory start state (observation :: observations) program
  | retire {start : Nat} {state : ArchState}
      {observation : RvfiObservation}
      {observations : List RvfiObservation}
      {instruction : FenceInstruction} {program : List FenceInstruction}
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state (fenceProgramInput memory instruction) observation
          { arch := fenceNext state instruction.kind,
            memory := memory }
          (fenceRetirement state (fenceProgramInput memory instruction) instruction.kind))
      (tail :
        FenceRvfiTrace memory (start + 1)
          (fenceNext state instruction.kind)
          observations program) :
      FenceRvfiTrace memory start state (observation :: observations)
        (instruction :: program)

/-- Every symbolic fence certificate is an ordinary RVFI normalization
certificate. -/
theorem FenceRvfiTrace.toRvfiTraceRefines
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List FenceInstruction}
    (certificate : FenceRvfiTrace memory start state observations program) :
    RvfiTraceRefines start observations
      (fenceProgramRetirements memory state program) := by
  induction certificate with
  | nil start state => exact .nil start
  | bubble hvalid tail ih => exact .bubble hvalid ih
  | retire horder boundary tail ih =>
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      exact .retire hspec.1 horder hretirement ih

/-- The executable normalizer accepts exactly the retirement stream specified
by an arbitrary `FenceRvfiTrace` certificate. -/
theorem FenceRvfiTrace.normalize
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List FenceInstruction}
    (certificate : FenceRvfiTrace memory start state observations program) :
    normalizeRvfiTrace? start observations =
      some (fenceProgramRetirements memory state program) :=
  (normalizeRvfiTrace?_iff).2 certificate.toRvfiTraceRefines

/-- The normalized symbolic fence stream is the stateful ISA trace for the same
program. -/
theorem FenceRvfiTrace.trace_refines
    (profile : PlatformProfile)
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List FenceInstruction}
    (certificate : FenceRvfiTrace memory start state observations program) :
    normalizeRvfiTrace? start observations =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (fenceProgramInputs memory program)) := by
  calc
    normalizeRvfiTrace? start observations =
        some (fenceProgramRetirements memory state program) :=
      certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (fenceProgramInputs memory program)) := by
      rw [rvMemoryMachineWith_fence_program_trace]

/-! ## Composing raw fence certificates -/

/-- Raw fence certificates compose at the next retirement order and folded
architectural state produced by the first program chunk. -/
theorem FenceRvfiTrace.append
    {memory : Memory} {start : Nat} {state : ArchState}
    {firstObservations secondObservations : List RvfiObservation}
    {firstProgram secondProgram : List FenceInstruction}
    (first : FenceRvfiTrace memory start state firstObservations firstProgram)
    (second : FenceRvfiTrace memory
      (start + firstProgram.length)
      (fenceProgramState state firstProgram)
      secondObservations secondProgram) :
    FenceRvfiTrace memory start state
      (firstObservations ++ secondObservations)
      (firstProgram ++ secondProgram) := by
  induction first with
  | nil start state =>
      simpa [fenceProgramState] using second
  | bubble hvalid tail ih =>
      refine FenceRvfiTrace.bubble hvalid ?_
      apply ih
      simpa [fenceProgramState] using second
  | retire horder boundary tail ih =>
      refine FenceRvfiTrace.retire horder boundary ?_
      apply ih
      simpa [fenceProgramState, List.length_cons, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using second

/-! ## Input-aware cycle certificate -/

/-- The fence invariant tied to an actual packed-RVFI cycle machine.  Bubble
cycles may carry any input; a retiring cycle must present the exact fence input
whose memory view it reports. -/
inductive FenceRvfiCycleTrace {State : Type}
    (machine : RvfiCycleMachine State) (memory : Memory) :
    Nat → State → ArchState → List Input → List FenceInstruction → Prop where
  | nil (start : Nat) (coreState : State) (state : ArchState) :
      FenceRvfiCycleTrace machine memory start coreState state [] []
  | bubble {start : Nat} {coreState coreState' : State}
      {state : ArchState} {cycleInput : Input} {cycles : List Input}
      {program : List FenceInstruction} {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hvalid : observation.valid = false)
      (tail : FenceRvfiCycleTrace machine memory start coreState' state
        cycles program) :
      FenceRvfiCycleTrace machine memory start coreState state
        (cycleInput :: cycles) program
  | retire {start : Nat} {coreState coreState' : State}
      {state : ArchState} {cycleInput : Input} {cycles : List Input}
      {instruction : FenceInstruction} {program : List FenceInstruction}
      {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hinput : cycleInput = fenceProgramInput memory instruction)
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state (fenceProgramInput memory instruction) observation
          { arch := fenceNext state instruction.kind,
            memory := memory }
          (fenceRetirement state (fenceProgramInput memory instruction) instruction.kind))
      (tail : FenceRvfiCycleTrace machine memory (start + 1) coreState'
        (fenceNext state instruction.kind)
        cycles program) :
      FenceRvfiCycleTrace machine memory start coreState state
        (cycleInput :: cycles) (instruction :: program)

/-- An input-aware fence certificate normalizes the observations emitted by its
actual cycle machine to the symbolic program's retirement stream. -/
theorem FenceRvfiCycleTrace.normalize
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List FenceInstruction}
    (certificate : FenceRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (fenceProgramRetirements memory state program) := by
  induction certificate with
  | nil start coreState state => rfl
  | bubble hstep hvalid tail ih =>
      simp only [rvfiObservations, hstep]
      simp [normalizeRvfiTrace?, hvalid, ih]
  | retire hstep hinput horder boundary tail ih =>
      simp only [rvfiObservations, hstep]
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      simp [normalizeRvfiTrace?, fenceProgramRetirements, hspec.1,
        horder, hretirement, ih]

/-- The cycle inputs retained by an input-aware fence certificate are exactly
the symbolic program inputs; bubbles are removed by the optional adapter. -/
theorem FenceRvfiCycleTrace.retireInputs_eq
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List FenceInstruction}
    (certificate : FenceRvfiCycleTrace machine memory start coreState state
      cycles program) :
    retireInputs machine.toCycleMachine coreState cycles =
      fenceProgramInputs memory program := by
  induction certificate with
  | nil start coreState state => rfl
  | @bubble start coreState coreState' state cycleInput cycles program
      observation hstep hvalid tail ih =>
      have hstep' :
          machine.toCycleMachine.step coreState cycleInput =
            (coreState', none) := by
        simp [RvfiCycleMachine.toCycleMachine, hstep,
          RvfiObservation.toRetirement?, hvalid]
      simp only [retireInputs, hstep']
      exact ih
  | @retire start coreState coreState' state cycleInput cycles
      instruction program observation hstep hinput horder boundary tail ih =>
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      have hstep' :
          machine.toCycleMachine.step coreState cycleInput =
            (coreState', some (fenceRetirement state (fenceProgramInput memory instruction) instruction.kind)) := by
        simp [RvfiCycleMachine.toCycleMachine, hstep, hretirement]
      simp only [retireInputs, hstep']
      rw [hinput]
      simpa [fenceProgramInputs] using ih

/-- Direct core-stream theorem: an input-aware fence certificate relates the
normalized packed observations to the stateful ISA trace on the machine's own
retiring inputs. -/
theorem FenceRvfiCycleTrace.trace_refines
    {State : Type} (profile : PlatformProfile)
    {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List FenceInstruction}
    (certificate : FenceRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
  calc
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
        some (fenceProgramRetirements memory state program) :=
      certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (fenceProgramInputs memory program)) := by
      rw [rvMemoryMachineWith_fence_program_trace]
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
      rw [certificate.retireInputs_eq]

/-! ## Composing input-aware cycle certificates -/

/-- Input-aware fence certificates compose at the exact state and retirement
order boundary produced by the first program chunk. -/
theorem FenceRvfiCycleTrace.append
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {firstCycles secondCycles : List Input}
    {firstProgram secondProgram : List FenceInstruction}
    (first : FenceRvfiCycleTrace machine memory start coreState state
      firstCycles firstProgram)
    (second : FenceRvfiCycleTrace machine memory
      (start + firstProgram.length)
      (rvfiStateAfter machine coreState firstCycles)
      (fenceProgramState state firstProgram)
      secondCycles secondProgram) :
    FenceRvfiCycleTrace machine memory start coreState state
      (firstCycles ++ secondCycles) (firstProgram ++ secondProgram) := by
  induction first with
  | nil start coreState state =>
      simpa [rvfiStateAfter, fenceProgramState] using second
  | bubble hstep hvalid tail ih =>
      refine FenceRvfiCycleTrace.bubble hstep hvalid ?_
      apply ih
      simpa [rvfiStateAfter, hstep] using second
  | retire hstep hinput horder boundary tail ih =>
      refine FenceRvfiCycleTrace.retire hstep hinput horder boundary ?_
      apply ih
      simpa [rvfiStateAfter, fenceProgramState, hstep, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using second

#print axioms LeanModels.Refine.fenceProgramInputs_append
#print axioms LeanModels.Refine.fenceProgramState_append
#print axioms LeanModels.Refine.fenceProgramRetirements_append
#print axioms LeanModels.Refine.rvMemoryMachineWith_fence_step
#print axioms LeanModels.Refine.rvMemoryMachineWith_fence_program_state
#print axioms LeanModels.Refine.rvMemoryMachineWith_fence_program_trace
#print axioms LeanModels.Refine.rvMemoryMachineWith_fence_program_state_append
#print axioms LeanModels.Refine.rvMemoryMachineWith_fence_program_trace_append
#print axioms LeanModels.Refine.FenceRvfiTrace.toRvfiTraceRefines
#print axioms LeanModels.Refine.FenceRvfiTrace.normalize
#print axioms LeanModels.Refine.FenceRvfiTrace.trace_refines
#print axioms LeanModels.Refine.FenceRvfiTrace.append
#print axioms LeanModels.Refine.FenceRvfiCycleTrace.normalize
#print axioms LeanModels.Refine.FenceRvfiCycleTrace.retireInputs_eq
#print axioms LeanModels.Refine.FenceRvfiCycleTrace.trace_refines
#print axioms LeanModels.Refine.FenceRvfiCycleTrace.append

end LeanModels.Refine
