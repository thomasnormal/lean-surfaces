import LeanModels.Refine.RvfiRv32i
import LeanModels.Refine.Rv32iSystem

/-!
# Symbolic RVFI programs made only of RV32I system instructions

`SystemInstruction` retains the fetched word, semantic system-operation kind,
and decoder proof.
The folds below carry an arbitrary system program through the stateful RV32I machine.  `SystemRvfiTrace` is the proof-facing
certificate for a packed RVFI stream: invalid rows are bubbles and every
retiring row supplies the indexed system boundary for the next architectural
state.

This is the system-family counterpart of `RvfiAddiProgram`.  It is deliberately a
program certificate rather than a core model; a loaded-core invariant still
has to establish the indexed `Rv32iBoundary` at each retiring cycle.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## A decoded system program -/

/-! The semantic system-operation shape retained by one decoded instruction. -/
structure SystemInstruction where
  word : Word
  kind : SysKind
  decode : Fetched.decode (.word word) = some (.system kind.toSysOp)

/-- The architectural input associated with one system instruction. -/
def systemProgramInput (memory : Memory) (instruction : SystemInstruction) : Input :=
  { fetched := .word instruction.word, memory := memory, irq := 0 }

/-- The cycle/commit inputs for a system program.  System instructions do not
mutate data memory, so every instruction sees the same threaded memory. -/
def systemProgramInputs (memory : Memory) : List SystemInstruction → List Input
  | [] => []
  | instruction :: program =>
      systemProgramInput memory instruction :: systemProgramInputs memory program

/-- The architectural state after executing a system program. -/
def systemProgramState (state : ArchState) : List SystemInstruction → ArchState
  | [] => state
  | instruction :: program =>
      systemProgramState
        (systemNext state instruction.kind) program

/-- The exact retirement stream for a system program. -/
def systemProgramRetirements (memory : Memory) (state : ArchState) :
    List SystemInstruction → List Retirement
  | [] => []
  | instruction :: program =>
      systemRetirement state (systemProgramInput memory instruction) instruction.kind ::
        systemProgramRetirements memory
          (systemNext state instruction.kind) program

/-! ## Program-fold composition -/

/-- The input fold preserves list concatenation. -/
theorem systemProgramInputs_append (memory : Memory)
    (first second : List SystemInstruction) :
    systemProgramInputs memory (first ++ second) =
      systemProgramInputs memory first ++ systemProgramInputs memory second := by
  induction first with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, systemProgramInputs, ih, List.cons_append]

/-- The architectural system fold resumes from the state reached by its prefix. -/
theorem systemProgramState_append (state : ArchState)
    (first second : List SystemInstruction) :
    systemProgramState state (first ++ second) =
      systemProgramState (systemProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, systemProgramState]
      exact ih (state :=
        systemNext state instruction.kind)

/-- The retirement fold carries the same architectural prefix boundary as the
state fold. -/
theorem systemProgramRetirements_append (memory : Memory) (state : ArchState)
    (first second : List SystemInstruction) :
    systemProgramRetirements memory state (first ++ second) =
      systemProgramRetirements memory state first ++
        systemProgramRetirements memory (systemProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, systemProgramRetirements]
      rw [ih (state :=
        systemNext state instruction.kind)]
      rfl

/-! ## Stateful ISA equations -/

/-- One decoded system instruction drives the exact stateful ISA transition
with no memory update. -/
theorem rvMemoryMachineWith_system_step
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (instruction : SystemInstruction) :
    (rvMemoryMachineWith profile).step
        { arch := state, memory := memory }
        (systemProgramInput memory instruction) =
      ({ arch := systemNext state instruction.kind, memory := memory },
        systemRetirement state (systemProgramInput memory instruction)
          instruction.kind) := by
  simp only [rvMemoryMachineWith, systemProgramInput]
  rw [isaStepWith_system profile state memory instruction.word instruction.kind
    instruction.decode]
  cases instruction.kind <;> rfl

/-- Threading the stateful ISA machine through every system instruction gives the
folded architectural state and unchanged memory. -/
theorem rvMemoryMachineWith_system_program_state
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (program : List SystemInstruction) :
    machineStateAfter (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (systemProgramInputs memory program) =
      { arch := systemProgramState state program, memory := memory } := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [systemProgramInputs, machineStateAfter]
      rw [rvMemoryMachineWith_system_step profile state memory instruction]
      simpa [systemProgramState] using
        (ih (state := systemNext state instruction.kind))

/-- The same system program has exactly the retirement stream prescribed by its
architectural fold. -/
theorem rvMemoryMachineWith_system_program_trace
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (program : List SystemInstruction) :
    trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (systemProgramInputs memory program) =
      systemProgramRetirements memory state program := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [systemProgramInputs, trace, systemProgramRetirements]
      change
        ((rvMemoryMachineWith profile).step
            { arch := state, memory := memory }
            (systemProgramInput memory instruction)).2 ::
          trace (rvMemoryMachineWith profile)
            ((rvMemoryMachineWith profile).step
              { arch := state, memory := memory }
              (systemProgramInput memory instruction)).1
            (systemProgramInputs memory program) = _
      rw [rvMemoryMachineWith_system_step profile state memory instruction]
      simpa using
        (ih (state := systemNext state instruction.kind))

/-- The stateful system machine resumes at the exact memory-machine state after
the first program segment. -/
theorem rvMemoryMachineWith_system_program_state_append
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (first second : List SystemInstruction) :
    machineStateAfter (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (systemProgramInputs memory (first ++ second)) =
      machineStateAfter (rvMemoryMachineWith profile)
        (machineStateAfter (rvMemoryMachineWith profile)
          { arch := state, memory := memory }
          (systemProgramInputs memory first))
        (systemProgramInputs memory second) := by
  rw [systemProgramInputs_append, machineStateAfter_append]

/-- The stateful system retirement stream splits at the same first-segment
boundary as the architectural state. -/
theorem rvMemoryMachineWith_system_program_trace_append
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (first second : List SystemInstruction) :
    trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (systemProgramInputs memory (first ++ second)) =
      trace (rvMemoryMachineWith profile)
          { arch := state, memory := memory }
          (systemProgramInputs memory first) ++
        trace (rvMemoryMachineWith profile)
          (machineStateAfter (rvMemoryMachineWith profile)
            { arch := state, memory := memory }
            (systemProgramInputs memory first))
          (systemProgramInputs memory second) := by
  rw [systemProgramInputs_append, machineTrace_append]

/-! ## Raw RVFI certificate for an arbitrary system program -/

/-- A raw RVFI stream whose retiring rows are exactly the supplied system
program. -/
inductive SystemRvfiTrace (memory : Memory) :
    Nat → ArchState → List RvfiObservation → List SystemInstruction → Prop where
  | nil (start : Nat) (state : ArchState) :
      SystemRvfiTrace memory start state [] []
  | bubble {start : Nat} {state : ArchState}
      {observation : RvfiObservation} {observations : List RvfiObservation}
      {program : List SystemInstruction}
      (hvalid : observation.valid = false)
      (tail : SystemRvfiTrace memory start state observations program) :
      SystemRvfiTrace memory start state (observation :: observations) program
  | retire {start : Nat} {state : ArchState}
      {observation : RvfiObservation}
      {observations : List RvfiObservation}
      {instruction : SystemInstruction} {program : List SystemInstruction}
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state (systemProgramInput memory instruction) observation
          { arch := systemNext state instruction.kind,
            memory := memory }
          (systemRetirement state (systemProgramInput memory instruction) instruction.kind))
      (tail :
        SystemRvfiTrace memory (start + 1)
          (systemNext state instruction.kind)
          observations program) :
      SystemRvfiTrace memory start state (observation :: observations)
        (instruction :: program)

/-- Every symbolic system certificate is an ordinary RVFI normalization
certificate. -/
theorem SystemRvfiTrace.toRvfiTraceRefines
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List SystemInstruction}
    (certificate : SystemRvfiTrace memory start state observations program) :
    RvfiTraceRefines start observations
      (systemProgramRetirements memory state program) := by
  induction certificate with
  | nil start state => exact .nil start
  | bubble hvalid tail ih => exact .bubble hvalid ih
  | retire horder boundary tail ih =>
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      exact .retire hspec.1 horder hretirement ih

/-- The executable normalizer accepts exactly the retirement stream specified
by an arbitrary `SystemRvfiTrace` certificate. -/
theorem SystemRvfiTrace.normalize
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List SystemInstruction}
    (certificate : SystemRvfiTrace memory start state observations program) :
    normalizeRvfiTrace? start observations =
      some (systemProgramRetirements memory state program) :=
  (normalizeRvfiTrace?_iff).2 certificate.toRvfiTraceRefines

/-- The normalized symbolic system stream is the stateful ISA trace for the same
program. -/
theorem SystemRvfiTrace.trace_refines
    (profile : PlatformProfile)
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List SystemInstruction}
    (certificate : SystemRvfiTrace memory start state observations program) :
    normalizeRvfiTrace? start observations =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (systemProgramInputs memory program)) := by
  calc
    normalizeRvfiTrace? start observations =
        some (systemProgramRetirements memory state program) :=
      certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (systemProgramInputs memory program)) := by
      rw [rvMemoryMachineWith_system_program_trace]

/-! ## Composing raw system certificates -/

/-- Raw system certificates compose at the next retirement order and folded
architectural state produced by the first program chunk. -/
theorem SystemRvfiTrace.append
    {memory : Memory} {start : Nat} {state : ArchState}
    {firstObservations secondObservations : List RvfiObservation}
    {firstProgram secondProgram : List SystemInstruction}
    (first : SystemRvfiTrace memory start state firstObservations firstProgram)
    (second : SystemRvfiTrace memory
      (start + firstProgram.length)
      (systemProgramState state firstProgram)
      secondObservations secondProgram) :
    SystemRvfiTrace memory start state
      (firstObservations ++ secondObservations)
      (firstProgram ++ secondProgram) := by
  induction first with
  | nil start state =>
      simpa [systemProgramState] using second
  | bubble hvalid tail ih =>
      refine SystemRvfiTrace.bubble hvalid ?_
      apply ih
      simpa [systemProgramState] using second
  | retire horder boundary tail ih =>
      refine SystemRvfiTrace.retire horder boundary ?_
      apply ih
      simpa [systemProgramState, List.length_cons, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using second

/-! ## Input-aware cycle certificate -/

/-- The system invariant tied to an actual packed-RVFI cycle machine.  Bubble
cycles may carry any input; a retiring cycle must present the exact system input
whose memory view it reports. -/
inductive SystemRvfiCycleTrace {State : Type}
    (machine : RvfiCycleMachine State) (memory : Memory) :
    Nat → State → ArchState → List Input → List SystemInstruction → Prop where
  | nil (start : Nat) (coreState : State) (state : ArchState) :
      SystemRvfiCycleTrace machine memory start coreState state [] []
  | bubble {start : Nat} {coreState coreState' : State}
      {state : ArchState} {cycleInput : Input} {cycles : List Input}
      {program : List SystemInstruction} {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hvalid : observation.valid = false)
      (tail : SystemRvfiCycleTrace machine memory start coreState' state
        cycles program) :
      SystemRvfiCycleTrace machine memory start coreState state
        (cycleInput :: cycles) program
  | retire {start : Nat} {coreState coreState' : State}
      {state : ArchState} {cycleInput : Input} {cycles : List Input}
      {instruction : SystemInstruction} {program : List SystemInstruction}
      {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hinput : cycleInput = systemProgramInput memory instruction)
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state (systemProgramInput memory instruction) observation
          { arch := systemNext state instruction.kind,
            memory := memory }
          (systemRetirement state (systemProgramInput memory instruction) instruction.kind))
      (tail : SystemRvfiCycleTrace machine memory (start + 1) coreState'
        (systemNext state instruction.kind)
        cycles program) :
      SystemRvfiCycleTrace machine memory start coreState state
        (cycleInput :: cycles) (instruction :: program)

/-- An input-aware system certificate normalizes the observations emitted by its
actual cycle machine to the symbolic program's retirement stream. -/
theorem SystemRvfiCycleTrace.normalize
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List SystemInstruction}
    (certificate : SystemRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (systemProgramRetirements memory state program) := by
  induction certificate with
  | nil start coreState state => rfl
  | bubble hstep hvalid tail ih =>
      simp only [rvfiObservations, hstep]
      simp [normalizeRvfiTrace?, hvalid, ih]
  | retire hstep hinput horder boundary tail ih =>
      simp only [rvfiObservations, hstep]
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      simp [normalizeRvfiTrace?, systemProgramRetirements, hspec.1,
        horder, hretirement, ih]

/-- The cycle inputs retained by an input-aware system certificate are exactly
the symbolic program inputs; bubbles are removed by the optional adapter. -/
theorem SystemRvfiCycleTrace.retireInputs_eq
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List SystemInstruction}
    (certificate : SystemRvfiCycleTrace machine memory start coreState state
      cycles program) :
    retireInputs machine.toCycleMachine coreState cycles =
      systemProgramInputs memory program := by
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
            (coreState', some (systemRetirement state (systemProgramInput memory instruction) instruction.kind)) := by
        simp [RvfiCycleMachine.toCycleMachine, hstep, hretirement]
      simp only [retireInputs, hstep']
      rw [hinput]
      simpa [systemProgramInputs] using ih

/-- Direct core-stream theorem: an input-aware system certificate relates the
normalized packed observations to the stateful ISA trace on the machine's own
retiring inputs. -/
theorem SystemRvfiCycleTrace.trace_refines
    {State : Type} (profile : PlatformProfile)
    {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List SystemInstruction}
    (certificate : SystemRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
  calc
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
        some (systemProgramRetirements memory state program) :=
      certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (systemProgramInputs memory program)) := by
      rw [rvMemoryMachineWith_system_program_trace]
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
      rw [certificate.retireInputs_eq]

/-! ## Composing input-aware cycle certificates -/

/-- Input-aware system certificates compose at the exact state and retirement
order boundary produced by the first program chunk. -/
theorem SystemRvfiCycleTrace.append
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {firstCycles secondCycles : List Input}
    {firstProgram secondProgram : List SystemInstruction}
    (first : SystemRvfiCycleTrace machine memory start coreState state
      firstCycles firstProgram)
    (second : SystemRvfiCycleTrace machine memory
      (start + firstProgram.length)
      (rvfiStateAfter machine coreState firstCycles)
      (systemProgramState state firstProgram)
      secondCycles secondProgram) :
    SystemRvfiCycleTrace machine memory start coreState state
      (firstCycles ++ secondCycles) (firstProgram ++ secondProgram) := by
  induction first with
  | nil start coreState state =>
      simpa [rvfiStateAfter, systemProgramState] using second
  | bubble hstep hvalid tail ih =>
      refine SystemRvfiCycleTrace.bubble hstep hvalid ?_
      apply ih
      simpa [rvfiStateAfter, hstep] using second
  | retire hstep hinput horder boundary tail ih =>
      refine SystemRvfiCycleTrace.retire hstep hinput horder boundary ?_
      apply ih
      simpa [rvfiStateAfter, systemProgramState, hstep, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using second

#print axioms LeanModels.Refine.systemProgramInputs_append
#print axioms LeanModels.Refine.systemProgramState_append
#print axioms LeanModels.Refine.systemProgramRetirements_append
#print axioms LeanModels.Refine.rvMemoryMachineWith_system_step
#print axioms LeanModels.Refine.rvMemoryMachineWith_system_program_state
#print axioms LeanModels.Refine.rvMemoryMachineWith_system_program_trace
#print axioms LeanModels.Refine.rvMemoryMachineWith_system_program_state_append
#print axioms LeanModels.Refine.rvMemoryMachineWith_system_program_trace_append
#print axioms LeanModels.Refine.SystemRvfiTrace.toRvfiTraceRefines
#print axioms LeanModels.Refine.SystemRvfiTrace.normalize
#print axioms LeanModels.Refine.SystemRvfiTrace.trace_refines
#print axioms LeanModels.Refine.SystemRvfiTrace.append
#print axioms LeanModels.Refine.SystemRvfiCycleTrace.normalize
#print axioms LeanModels.Refine.SystemRvfiCycleTrace.retireInputs_eq
#print axioms LeanModels.Refine.SystemRvfiCycleTrace.trace_refines
#print axioms LeanModels.Refine.SystemRvfiCycleTrace.append

end LeanModels.Refine
