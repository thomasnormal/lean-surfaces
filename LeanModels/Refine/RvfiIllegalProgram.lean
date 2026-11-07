import LeanModels.Refine.RvfiRv32i
import LeanModels.Refine.Rv32iTrap

/-!
# Symbolic RVFI programs made only of RV32I illegal instructions

`IllegalInstruction` retains the fetched word and its proof of decode failure.
The folds below carry an arbitrary illegal program through the stateful RV32I machine.  `IllegalRvfiTrace` is the proof-facing
certificate for a packed RVFI stream: invalid rows are bubbles and every
retiring row supplies the indexed illegal boundary for the next architectural
state.

This is the illegal-family counterpart of `RvfiAddiProgram`.  It is deliberately a
program certificate rather than a core model; a loaded-core invariant still
has to establish the indexed `Rv32iBoundary` at each retiring cycle.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## A decoded illegal program -/

/-! The undecodable shape retained by one decoded instruction. -/
structure IllegalInstruction where
  word : Word
  decode : Fetched.decode (.word word) = none

/-- The architectural input associated with one illegal instruction. -/
def illegalProgramInput (memory : Memory) (instruction : IllegalInstruction) : Input :=
  { fetched := .word instruction.word, memory := memory, irq := 0 }

/-- The cycle/commit inputs for an illegal program.  Illegal instructions do not
mutate data memory, so every instruction sees the same threaded memory. -/
def illegalProgramInputs (memory : Memory) : List IllegalInstruction → List Input
  | [] => []
  | instruction :: program =>
      illegalProgramInput memory instruction :: illegalProgramInputs memory program

/-- The architectural state after executing a illegal program. -/
def illegalProgramState (state : ArchState) : List IllegalInstruction → ArchState
  | [] => state
  | _ :: program =>
      illegalProgramState
        (illegalNext state) program

/-- The exact retirement stream for an illegal program. -/
def illegalProgramRetirements (memory : Memory) (state : ArchState) :
    List IllegalInstruction → List Retirement
  | [] => []
  | instruction :: program =>
      illegalRetirement state (illegalProgramInput memory instruction) ::
        illegalProgramRetirements memory
          (illegalNext state) program

/-! ## Program-fold composition -/

/-- The input fold preserves list concatenation. -/
theorem illegalProgramInputs_append (memory : Memory)
    (first second : List IllegalInstruction) :
    illegalProgramInputs memory (first ++ second) =
      illegalProgramInputs memory first ++ illegalProgramInputs memory second := by
  induction first with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, illegalProgramInputs, ih, List.cons_append]

/-- The architectural illegal fold resumes from the state reached by its prefix. -/
theorem illegalProgramState_append (state : ArchState)
    (first second : List IllegalInstruction) :
    illegalProgramState state (first ++ second) =
      illegalProgramState (illegalProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, illegalProgramState]
      exact ih (state :=
        illegalNext state)

/-- The retirement fold carries the same architectural prefix boundary as the
state fold. -/
theorem illegalProgramRetirements_append (memory : Memory) (state : ArchState)
    (first second : List IllegalInstruction) :
    illegalProgramRetirements memory state (first ++ second) =
      illegalProgramRetirements memory state first ++
        illegalProgramRetirements memory (illegalProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, illegalProgramRetirements]
      rw [ih (state :=
        illegalNext state)]
      rfl

/-! ## Stateful ISA equations -/

/-- One decoded illegal instruction drives the exact stateful ISA transition
with no memory update. -/
theorem rvMemoryMachineWith_illegal_step
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (instruction : IllegalInstruction) :
    (rvMemoryMachineWith profile).step
        { arch := state, memory := memory }
        (illegalProgramInput memory instruction) =
      ({ arch := illegalNext state, memory := memory },
        illegalRetirement state (illegalProgramInput memory instruction)) := by
  simp only [rvMemoryMachineWith, illegalProgramInput]
  rw [isaStepWith_illegal profile state memory instruction.word
    instruction.decode]
  rfl

/-- Threading the stateful ISA machine through every illegal instruction gives the
folded architectural state and unchanged memory. -/
theorem rvMemoryMachineWith_illegal_program_state
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (program : List IllegalInstruction) :
    machineStateAfter (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (illegalProgramInputs memory program) =
      { arch := illegalProgramState state program, memory := memory } := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [illegalProgramInputs, machineStateAfter]
      rw [rvMemoryMachineWith_illegal_step profile state memory instruction]
      simpa [illegalProgramState] using
        (ih (state := illegalNext state))

/-- The same illegal program has exactly the retirement stream prescribed by its
architectural fold. -/
theorem rvMemoryMachineWith_illegal_program_trace
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (program : List IllegalInstruction) :
    trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (illegalProgramInputs memory program) =
      illegalProgramRetirements memory state program := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [illegalProgramInputs, trace, illegalProgramRetirements]
      change
        ((rvMemoryMachineWith profile).step
            { arch := state, memory := memory }
            (illegalProgramInput memory instruction)).2 ::
          trace (rvMemoryMachineWith profile)
            ((rvMemoryMachineWith profile).step
              { arch := state, memory := memory }
              (illegalProgramInput memory instruction)).1
            (illegalProgramInputs memory program) = _
      rw [rvMemoryMachineWith_illegal_step profile state memory instruction]
      simpa using
        (ih (state := illegalNext state))

/-- The stateful illegal machine resumes at the exact memory-machine state after
the first program segment. -/
theorem rvMemoryMachineWith_illegal_program_state_append
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (first second : List IllegalInstruction) :
    machineStateAfter (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (illegalProgramInputs memory (first ++ second)) =
      machineStateAfter (rvMemoryMachineWith profile)
        (machineStateAfter (rvMemoryMachineWith profile)
          { arch := state, memory := memory }
          (illegalProgramInputs memory first))
        (illegalProgramInputs memory second) := by
  rw [illegalProgramInputs_append, machineStateAfter_append]

/-- The stateful illegal retirement stream splits at the same first-segment
boundary as the architectural state. -/
theorem rvMemoryMachineWith_illegal_program_trace_append
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (first second : List IllegalInstruction) :
    trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (illegalProgramInputs memory (first ++ second)) =
      trace (rvMemoryMachineWith profile)
          { arch := state, memory := memory }
          (illegalProgramInputs memory first) ++
        trace (rvMemoryMachineWith profile)
          (machineStateAfter (rvMemoryMachineWith profile)
            { arch := state, memory := memory }
            (illegalProgramInputs memory first))
          (illegalProgramInputs memory second) := by
  rw [illegalProgramInputs_append, machineTrace_append]

/-! ## Raw RVFI certificate for an arbitrary illegal program -/

/-- A raw RVFI stream whose retiring rows are exactly the supplied illegal
program. -/
inductive IllegalRvfiTrace (memory : Memory) :
    Nat → ArchState → List RvfiObservation → List IllegalInstruction → Prop where
  | nil (start : Nat) (state : ArchState) :
      IllegalRvfiTrace memory start state [] []
  | bubble {start : Nat} {state : ArchState}
      {observation : RvfiObservation} {observations : List RvfiObservation}
      {program : List IllegalInstruction}
      (hvalid : observation.valid = false)
      (tail : IllegalRvfiTrace memory start state observations program) :
      IllegalRvfiTrace memory start state (observation :: observations) program
  | retire {start : Nat} {state : ArchState}
      {observation : RvfiObservation}
      {observations : List RvfiObservation}
      {instruction : IllegalInstruction} {program : List IllegalInstruction}
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state (illegalProgramInput memory instruction) observation
          { arch := illegalNext state,
            memory := memory }
          (illegalRetirement state (illegalProgramInput memory instruction)))
      (tail :
        IllegalRvfiTrace memory (start + 1)
          (illegalNext state)
          observations program) :
      IllegalRvfiTrace memory start state (observation :: observations)
        (instruction :: program)

/-- Every symbolic illegal certificate is an ordinary RVFI normalization
certificate. -/
theorem IllegalRvfiTrace.toRvfiTraceRefines
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List IllegalInstruction}
    (certificate : IllegalRvfiTrace memory start state observations program) :
    RvfiTraceRefines start observations
      (illegalProgramRetirements memory state program) := by
  induction certificate with
  | nil start state => exact .nil start
  | bubble hvalid tail ih => exact .bubble hvalid ih
  | retire horder boundary tail ih =>
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      exact .retire hspec.1 horder hretirement ih

/-- The executable normalizer accepts exactly the retirement stream specified
by an arbitrary `IllegalRvfiTrace` certificate. -/
theorem IllegalRvfiTrace.normalize
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List IllegalInstruction}
    (certificate : IllegalRvfiTrace memory start state observations program) :
    normalizeRvfiTrace? start observations =
      some (illegalProgramRetirements memory state program) :=
  (normalizeRvfiTrace?_iff).2 certificate.toRvfiTraceRefines

/-- The normalized symbolic illegal stream is the stateful ISA trace for the same
program. -/
theorem IllegalRvfiTrace.trace_refines
    (profile : PlatformProfile)
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List IllegalInstruction}
    (certificate : IllegalRvfiTrace memory start state observations program) :
    normalizeRvfiTrace? start observations =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (illegalProgramInputs memory program)) := by
  calc
    normalizeRvfiTrace? start observations =
        some (illegalProgramRetirements memory state program) :=
      certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (illegalProgramInputs memory program)) := by
      rw [rvMemoryMachineWith_illegal_program_trace]

/-! ## Composing raw illegal certificates -/

/-- Raw illegal certificates compose at the next retirement order and folded
architectural state produced by the first program chunk. -/
theorem IllegalRvfiTrace.append
    {memory : Memory} {start : Nat} {state : ArchState}
    {firstObservations secondObservations : List RvfiObservation}
    {firstProgram secondProgram : List IllegalInstruction}
    (first : IllegalRvfiTrace memory start state firstObservations firstProgram)
    (second : IllegalRvfiTrace memory
      (start + firstProgram.length)
      (illegalProgramState state firstProgram)
      secondObservations secondProgram) :
    IllegalRvfiTrace memory start state
      (firstObservations ++ secondObservations)
      (firstProgram ++ secondProgram) := by
  induction first with
  | nil start state =>
      simpa [illegalProgramState] using second
  | bubble hvalid tail ih =>
      refine IllegalRvfiTrace.bubble hvalid ?_
      apply ih
      simpa [illegalProgramState] using second
  | retire horder boundary tail ih =>
      refine IllegalRvfiTrace.retire horder boundary ?_
      apply ih
      simpa [illegalProgramState, List.length_cons, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using second

/-! ## Input-aware cycle certificate -/

/-- The illegal invariant tied to an actual packed-RVFI cycle machine.  Bubble
cycles may carry any input; a retiring cycle must present the exact illegal input
whose memory view it reports. -/
inductive IllegalRvfiCycleTrace {State : Type}
    (machine : RvfiCycleMachine State) (memory : Memory) :
    Nat → State → ArchState → List Input → List IllegalInstruction → Prop where
  | nil (start : Nat) (coreState : State) (state : ArchState) :
      IllegalRvfiCycleTrace machine memory start coreState state [] []
  | bubble {start : Nat} {coreState coreState' : State}
      {state : ArchState} {cycleInput : Input} {cycles : List Input}
      {program : List IllegalInstruction} {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hvalid : observation.valid = false)
      (tail : IllegalRvfiCycleTrace machine memory start coreState' state
        cycles program) :
      IllegalRvfiCycleTrace machine memory start coreState state
        (cycleInput :: cycles) program
  | retire {start : Nat} {coreState coreState' : State}
      {state : ArchState} {cycleInput : Input} {cycles : List Input}
      {instruction : IllegalInstruction} {program : List IllegalInstruction}
      {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hinput : cycleInput = illegalProgramInput memory instruction)
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state (illegalProgramInput memory instruction) observation
          { arch := illegalNext state,
            memory := memory }
          (illegalRetirement state (illegalProgramInput memory instruction)))
      (tail : IllegalRvfiCycleTrace machine memory (start + 1) coreState'
        (illegalNext state)
        cycles program) :
      IllegalRvfiCycleTrace machine memory start coreState state
        (cycleInput :: cycles) (instruction :: program)

/-- An input-aware illegal certificate normalizes the observations emitted by its
actual cycle machine to the symbolic program's retirement stream. -/
theorem IllegalRvfiCycleTrace.normalize
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List IllegalInstruction}
    (certificate : IllegalRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (illegalProgramRetirements memory state program) := by
  induction certificate with
  | nil start coreState state => rfl
  | bubble hstep hvalid tail ih =>
      simp only [rvfiObservations, hstep]
      simp [normalizeRvfiTrace?, hvalid, ih]
  | retire hstep hinput horder boundary tail ih =>
      simp only [rvfiObservations, hstep]
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      simp [normalizeRvfiTrace?, illegalProgramRetirements, hspec.1,
        horder, hretirement, ih]

/-- The cycle inputs retained by an input-aware illegal certificate are exactly
the symbolic program inputs; bubbles are removed by the optional adapter. -/
theorem IllegalRvfiCycleTrace.retireInputs_eq
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List IllegalInstruction}
    (certificate : IllegalRvfiCycleTrace machine memory start coreState state
      cycles program) :
    retireInputs machine.toCycleMachine coreState cycles =
      illegalProgramInputs memory program := by
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
            (coreState', some (illegalRetirement state (illegalProgramInput memory instruction))) := by
        simp [RvfiCycleMachine.toCycleMachine, hstep, hretirement]
      simp only [retireInputs, hstep']
      rw [hinput]
      simpa [illegalProgramInputs] using ih

/-- Direct core-stream theorem: an input-aware illegal certificate relates the
normalized packed observations to the stateful ISA trace on the machine's own
retiring inputs. -/
theorem IllegalRvfiCycleTrace.trace_refines
    {State : Type} (profile : PlatformProfile)
    {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List IllegalInstruction}
    (certificate : IllegalRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
  calc
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
        some (illegalProgramRetirements memory state program) :=
      certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (illegalProgramInputs memory program)) := by
      rw [rvMemoryMachineWith_illegal_program_trace]
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
      rw [certificate.retireInputs_eq]

/-! ## Composing input-aware cycle certificates -/

/-- Input-aware illegal certificates compose at the exact state and retirement
order boundary produced by the first program chunk. -/
theorem IllegalRvfiCycleTrace.append
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {firstCycles secondCycles : List Input}
    {firstProgram secondProgram : List IllegalInstruction}
    (first : IllegalRvfiCycleTrace machine memory start coreState state
      firstCycles firstProgram)
    (second : IllegalRvfiCycleTrace machine memory
      (start + firstProgram.length)
      (rvfiStateAfter machine coreState firstCycles)
      (illegalProgramState state firstProgram)
      secondCycles secondProgram) :
    IllegalRvfiCycleTrace machine memory start coreState state
      (firstCycles ++ secondCycles) (firstProgram ++ secondProgram) := by
  induction first with
  | nil start coreState state =>
      simpa [rvfiStateAfter, illegalProgramState] using second
  | bubble hstep hvalid tail ih =>
      refine IllegalRvfiCycleTrace.bubble hstep hvalid ?_
      apply ih
      simpa [rvfiStateAfter, hstep] using second
  | retire hstep hinput horder boundary tail ih =>
      refine IllegalRvfiCycleTrace.retire hstep hinput horder boundary ?_
      apply ih
      simpa [rvfiStateAfter, illegalProgramState, hstep, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using second

#print axioms LeanModels.Refine.illegalProgramInputs_append
#print axioms LeanModels.Refine.illegalProgramState_append
#print axioms LeanModels.Refine.illegalProgramRetirements_append
#print axioms LeanModels.Refine.rvMemoryMachineWith_illegal_step
#print axioms LeanModels.Refine.rvMemoryMachineWith_illegal_program_state
#print axioms LeanModels.Refine.rvMemoryMachineWith_illegal_program_trace
#print axioms LeanModels.Refine.rvMemoryMachineWith_illegal_program_state_append
#print axioms LeanModels.Refine.rvMemoryMachineWith_illegal_program_trace_append
#print axioms LeanModels.Refine.IllegalRvfiTrace.toRvfiTraceRefines
#print axioms LeanModels.Refine.IllegalRvfiTrace.normalize
#print axioms LeanModels.Refine.IllegalRvfiTrace.trace_refines
#print axioms LeanModels.Refine.IllegalRvfiTrace.append
#print axioms LeanModels.Refine.IllegalRvfiCycleTrace.normalize
#print axioms LeanModels.Refine.IllegalRvfiCycleTrace.retireInputs_eq
#print axioms LeanModels.Refine.IllegalRvfiCycleTrace.trace_refines
#print axioms LeanModels.Refine.IllegalRvfiCycleTrace.append

end LeanModels.Refine
