import LeanModels.Refine.RvfiRv32i
import LeanModels.Refine.Rv32iCsr

/-!
# Symbolic RVFI programs made only of RV32I CSR instructions

`CsrInstruction` retains the fetched word, semantic CSR operation kind, row, and decoder proofs.
The folds below carry an arbitrary CSR program through the stateful RV32I machine.  `CsrRvfiTrace` is the proof-facing
certificate for a packed RVFI stream: invalid rows are bubbles and every
retiring row supplies the indexed CSR boundary for the next architectural
state.

This is the CSR-family counterpart of `RvfiAddiProgram`.  It is deliberately a
program certificate rather than a core model; a loaded-core invariant still
has to establish the indexed `Rv32iBoundary` at each retiring cycle.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## A decoded CSR program -/

/-! The semantic csr-operation shape retained by one decoded instruction. -/
structure CsrInstruction where
  word : Word
  kind : CsrOpKind
  row : CsrBehavior
  decode : Fetched.decode (.word word) = some kind.toInstr
  rowLookup : findCsr? kind.addr = some row

/-- The architectural input associated with one CSR instruction. -/
def csrProgramInput (memory : Memory) (instruction : CsrInstruction) : Input :=
  { fetched := .word instruction.word, memory := memory, irq := 0 }

/-- The cycle/commit inputs for a CSR program.  Zicsr instructions do not
mutate data memory, so every instruction sees the same threaded memory. -/
def csrProgramInputs (memory : Memory) : List CsrInstruction → List Input
  | [] => []
  | instruction :: program =>
      csrProgramInput memory instruction :: csrProgramInputs memory program

/-- The architectural state after executing a CSR program. -/
def csrProgramState (state : ArchState) : List CsrInstruction → ArchState
  | [] => state
  | instruction :: program =>
      csrProgramState
        (csrNext state instruction.row instruction.kind) program

/-- The exact retirement stream for a CSR program. -/
def csrProgramRetirements (memory : Memory) (state : ArchState) :
    List CsrInstruction → List Retirement
  | [] => []
  | instruction :: program =>
      csrRetirement state (csrProgramInput memory instruction)
          instruction.row instruction.kind ::
        csrProgramRetirements memory
          (csrNext state instruction.row instruction.kind) program

/-! ## Program-fold composition -/

/-- The input fold preserves list concatenation. -/
theorem csrProgramInputs_append (memory : Memory)
    (first second : List CsrInstruction) :
    csrProgramInputs memory (first ++ second) =
      csrProgramInputs memory first ++ csrProgramInputs memory second := by
  induction first with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, csrProgramInputs, ih, List.cons_append]

/-- The architectural CSR fold resumes from the state reached by its prefix. -/
theorem csrProgramState_append (state : ArchState)
    (first second : List CsrInstruction) :
    csrProgramState state (first ++ second) =
      csrProgramState (csrProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, csrProgramState]
      exact ih (state :=
        csrNext state instruction.row instruction.kind)

/-- The retirement fold carries the same architectural prefix boundary as the
state fold. -/
theorem csrProgramRetirements_append (memory : Memory) (state : ArchState)
    (first second : List CsrInstruction) :
    csrProgramRetirements memory state (first ++ second) =
      csrProgramRetirements memory state first ++
        csrProgramRetirements memory (csrProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, csrProgramRetirements]
      rw [ih (state :=
        csrNext state instruction.row instruction.kind)]
      rfl

/-! ## Stateful ISA equations -/

/-- One decoded CSR instruction drives the exact stateful ISA transition
with no memory update. -/
theorem rvMemoryMachineWith_csr_step
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (instruction : CsrInstruction) :
    (rvMemoryMachineWith profile).step
        { arch := state, memory := memory }
        (csrProgramInput memory instruction) =
      ({ arch := csrNext state instruction.row instruction.kind, memory := memory },
        csrRetirement state (csrProgramInput memory instruction)
          instruction.row instruction.kind) := by
  simp only [rvMemoryMachineWith, csrProgramInput]
  rw [isaStepWith_csr profile state memory instruction.word instruction.row instruction.kind
    instruction.decode instruction.rowLookup]
  rfl

/-- Threading the stateful ISA machine through every CSR instruction gives the
folded architectural state and unchanged memory. -/
theorem rvMemoryMachineWith_csr_program_state
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (program : List CsrInstruction) :
    machineStateAfter (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (csrProgramInputs memory program) =
      { arch := csrProgramState state program, memory := memory } := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [csrProgramInputs, machineStateAfter]
      rw [rvMemoryMachineWith_csr_step profile state memory instruction]
      simpa [csrProgramState] using
        (ih (state := csrNext state instruction.row instruction.kind))

/-- The same CSR program has exactly the retirement stream prescribed by its
architectural fold. -/
theorem rvMemoryMachineWith_csr_program_trace
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (program : List CsrInstruction) :
    trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (csrProgramInputs memory program) =
      csrProgramRetirements memory state program := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [csrProgramInputs, trace, csrProgramRetirements]
      change
        ((rvMemoryMachineWith profile).step
            { arch := state, memory := memory }
            (csrProgramInput memory instruction)).2 ::
          trace (rvMemoryMachineWith profile)
            ((rvMemoryMachineWith profile).step
              { arch := state, memory := memory }
              (csrProgramInput memory instruction)).1
            (csrProgramInputs memory program) = _
      rw [rvMemoryMachineWith_csr_step profile state memory instruction]
      simpa using
        (ih (state := csrNext state instruction.row instruction.kind))

/-- The stateful csr machine resumes at the exact memory-machine state after
the first program segment. -/
theorem rvMemoryMachineWith_csr_program_state_append
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (first second : List CsrInstruction) :
    machineStateAfter (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (csrProgramInputs memory (first ++ second)) =
      machineStateAfter (rvMemoryMachineWith profile)
        (machineStateAfter (rvMemoryMachineWith profile)
          { arch := state, memory := memory }
          (csrProgramInputs memory first))
        (csrProgramInputs memory second) := by
  rw [csrProgramInputs_append, machineStateAfter_append]

/-- The stateful csr retirement stream splits at the same first-segment
boundary as the architectural state. -/
theorem rvMemoryMachineWith_csr_program_trace_append
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (first second : List CsrInstruction) :
    trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (csrProgramInputs memory (first ++ second)) =
      trace (rvMemoryMachineWith profile)
          { arch := state, memory := memory }
          (csrProgramInputs memory first) ++
        trace (rvMemoryMachineWith profile)
          (machineStateAfter (rvMemoryMachineWith profile)
            { arch := state, memory := memory }
            (csrProgramInputs memory first))
          (csrProgramInputs memory second) := by
  rw [csrProgramInputs_append, machineTrace_append]

/-! ## Raw RVFI certificate for an arbitrary CSR program -/

/-- A raw RVFI stream whose retiring rows are exactly the supplied csr
program. -/
inductive CsrRvfiTrace (memory : Memory) :
    Nat → ArchState → List RvfiObservation → List CsrInstruction → Prop where
  | nil (start : Nat) (state : ArchState) :
      CsrRvfiTrace memory start state [] []
  | bubble {start : Nat} {state : ArchState}
      {observation : RvfiObservation} {observations : List RvfiObservation}
      {program : List CsrInstruction}
      (hvalid : observation.valid = false)
      (tail : CsrRvfiTrace memory start state observations program) :
      CsrRvfiTrace memory start state (observation :: observations) program
  | retire {start : Nat} {state : ArchState}
      {observation : RvfiObservation}
      {observations : List RvfiObservation}
      {instruction : CsrInstruction} {program : List CsrInstruction}
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state (csrProgramInput memory instruction) observation
          { arch := csrNext state instruction.row instruction.kind,
            memory := memory }
          (csrRetirement state (csrProgramInput memory instruction)
          instruction.row instruction.kind))
      (tail :
        CsrRvfiTrace memory (start + 1)
          (csrNext state instruction.row instruction.kind)
          observations program) :
      CsrRvfiTrace memory start state (observation :: observations)
        (instruction :: program)

/-- Every symbolic CSR certificate is an ordinary RVFI normalization
certificate. -/
theorem CsrRvfiTrace.toRvfiTraceRefines
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List CsrInstruction}
    (certificate : CsrRvfiTrace memory start state observations program) :
    RvfiTraceRefines start observations
      (csrProgramRetirements memory state program) := by
  induction certificate with
  | nil start state => exact .nil start
  | bubble hvalid tail ih => exact .bubble hvalid ih
  | retire horder boundary tail ih =>
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      exact .retire hspec.1 horder hretirement ih

/-- The executable normalizer accepts exactly the retirement stream specified
by an arbitrary `CsrRvfiTrace` certificate. -/
theorem CsrRvfiTrace.normalize
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List CsrInstruction}
    (certificate : CsrRvfiTrace memory start state observations program) :
    normalizeRvfiTrace? start observations =
      some (csrProgramRetirements memory state program) :=
  (normalizeRvfiTrace?_iff).2 certificate.toRvfiTraceRefines

/-- The normalized symbolic CSR stream is the stateful ISA trace for the same
program. -/
theorem CsrRvfiTrace.trace_refines
    (profile : PlatformProfile)
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List CsrInstruction}
    (certificate : CsrRvfiTrace memory start state observations program) :
    normalizeRvfiTrace? start observations =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (csrProgramInputs memory program)) := by
  calc
    normalizeRvfiTrace? start observations =
        some (csrProgramRetirements memory state program) :=
      certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (csrProgramInputs memory program)) := by
      rw [rvMemoryMachineWith_csr_program_trace]

/-! ## Composing raw CSR certificates -/

/-- Raw CSR certificates compose at the next retirement order and folded
architectural state produced by the first program chunk. -/
theorem CsrRvfiTrace.append
    {memory : Memory} {start : Nat} {state : ArchState}
    {firstObservations secondObservations : List RvfiObservation}
    {firstProgram secondProgram : List CsrInstruction}
    (first : CsrRvfiTrace memory start state firstObservations firstProgram)
    (second : CsrRvfiTrace memory
      (start + firstProgram.length)
      (csrProgramState state firstProgram)
      secondObservations secondProgram) :
    CsrRvfiTrace memory start state
      (firstObservations ++ secondObservations)
      (firstProgram ++ secondProgram) := by
  induction first with
  | nil start state =>
      simpa [csrProgramState] using second
  | bubble hvalid tail ih =>
      refine CsrRvfiTrace.bubble hvalid ?_
      apply ih
      simpa [csrProgramState] using second
  | retire horder boundary tail ih =>
      refine CsrRvfiTrace.retire horder boundary ?_
      apply ih
      simpa [csrProgramState, List.length_cons, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using second

/-! ## Input-aware cycle certificate -/

/-- The csr invariant tied to an actual packed-RVFI cycle machine.  Bubble
cycles may carry any input; a retiring cycle must present the exact csr input
whose memory view it reports. -/
inductive CsrRvfiCycleTrace {State : Type}
    (machine : RvfiCycleMachine State) (memory : Memory) :
    Nat → State → ArchState → List Input → List CsrInstruction → Prop where
  | nil (start : Nat) (coreState : State) (state : ArchState) :
      CsrRvfiCycleTrace machine memory start coreState state [] []
  | bubble {start : Nat} {coreState coreState' : State}
      {state : ArchState} {cycleInput : Input} {cycles : List Input}
      {program : List CsrInstruction} {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hvalid : observation.valid = false)
      (tail : CsrRvfiCycleTrace machine memory start coreState' state
        cycles program) :
      CsrRvfiCycleTrace machine memory start coreState state
        (cycleInput :: cycles) program
  | retire {start : Nat} {coreState coreState' : State}
      {state : ArchState} {cycleInput : Input} {cycles : List Input}
      {instruction : CsrInstruction} {program : List CsrInstruction}
      {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hinput : cycleInput = csrProgramInput memory instruction)
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state (csrProgramInput memory instruction) observation
          { arch := csrNext state instruction.row instruction.kind,
            memory := memory }
          (csrRetirement state (csrProgramInput memory instruction)
          instruction.row instruction.kind))
      (tail : CsrRvfiCycleTrace machine memory (start + 1) coreState'
        (csrNext state instruction.row instruction.kind)
        cycles program) :
      CsrRvfiCycleTrace machine memory start coreState state
        (cycleInput :: cycles) (instruction :: program)

/-- An input-aware CSR certificate normalizes the observations emitted by its
actual cycle machine to the symbolic program's retirement stream. -/
theorem CsrRvfiCycleTrace.normalize
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List CsrInstruction}
    (certificate : CsrRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (csrProgramRetirements memory state program) := by
  induction certificate with
  | nil start coreState state => rfl
  | bubble hstep hvalid tail ih =>
      simp only [rvfiObservations, hstep]
      simp [normalizeRvfiTrace?, hvalid, ih]
  | retire hstep hinput horder boundary tail ih =>
      simp only [rvfiObservations, hstep]
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      simp [normalizeRvfiTrace?, csrProgramRetirements, hspec.1,
        horder, hretirement, ih]

/-- The cycle inputs retained by an input-aware CSR certificate are exactly
the symbolic program inputs; bubbles are removed by the optional adapter. -/
theorem CsrRvfiCycleTrace.retireInputs_eq
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List CsrInstruction}
    (certificate : CsrRvfiCycleTrace machine memory start coreState state
      cycles program) :
    retireInputs machine.toCycleMachine coreState cycles =
      csrProgramInputs memory program := by
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
            (coreState', some (csrRetirement state (csrProgramInput memory instruction)
          instruction.row instruction.kind)) := by
        simp [RvfiCycleMachine.toCycleMachine, hstep, hretirement]
      simp only [retireInputs, hstep']
      rw [hinput]
      simpa [csrProgramInputs] using ih

/-- Direct core-stream theorem: an input-aware CSR certificate relates the
normalized packed observations to the stateful ISA trace on the machine's own
retiring inputs. -/
theorem CsrRvfiCycleTrace.trace_refines
    {State : Type} (profile : PlatformProfile)
    {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List CsrInstruction}
    (certificate : CsrRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
  calc
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
        some (csrProgramRetirements memory state program) :=
      certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (csrProgramInputs memory program)) := by
      rw [rvMemoryMachineWith_csr_program_trace]
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
      rw [certificate.retireInputs_eq]

/-! ## Composing input-aware cycle certificates -/

/-- Input-aware CSR certificates compose at the exact state and retirement
order boundary produced by the first program chunk. -/
theorem CsrRvfiCycleTrace.append
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {firstCycles secondCycles : List Input}
    {firstProgram secondProgram : List CsrInstruction}
    (first : CsrRvfiCycleTrace machine memory start coreState state
      firstCycles firstProgram)
    (second : CsrRvfiCycleTrace machine memory
      (start + firstProgram.length)
      (rvfiStateAfter machine coreState firstCycles)
      (csrProgramState state firstProgram)
      secondCycles secondProgram) :
    CsrRvfiCycleTrace machine memory start coreState state
      (firstCycles ++ secondCycles) (firstProgram ++ secondProgram) := by
  induction first with
  | nil start coreState state =>
      simpa [rvfiStateAfter, csrProgramState] using second
  | bubble hstep hvalid tail ih =>
      refine CsrRvfiCycleTrace.bubble hstep hvalid ?_
      apply ih
      simpa [rvfiStateAfter, hstep] using second
  | retire hstep hinput horder boundary tail ih =>
      refine CsrRvfiCycleTrace.retire hstep hinput horder boundary ?_
      apply ih
      simpa [rvfiStateAfter, csrProgramState, hstep, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using second

#print axioms LeanModels.Refine.csrProgramInputs_append
#print axioms LeanModels.Refine.csrProgramState_append
#print axioms LeanModels.Refine.csrProgramRetirements_append
#print axioms LeanModels.Refine.rvMemoryMachineWith_csr_step
#print axioms LeanModels.Refine.rvMemoryMachineWith_csr_program_state
#print axioms LeanModels.Refine.rvMemoryMachineWith_csr_program_trace
#print axioms LeanModels.Refine.rvMemoryMachineWith_csr_program_state_append
#print axioms LeanModels.Refine.rvMemoryMachineWith_csr_program_trace_append
#print axioms LeanModels.Refine.CsrRvfiTrace.toRvfiTraceRefines
#print axioms LeanModels.Refine.CsrRvfiTrace.normalize
#print axioms LeanModels.Refine.CsrRvfiTrace.trace_refines
#print axioms LeanModels.Refine.CsrRvfiTrace.append
#print axioms LeanModels.Refine.CsrRvfiCycleTrace.normalize
#print axioms LeanModels.Refine.CsrRvfiCycleTrace.retireInputs_eq
#print axioms LeanModels.Refine.CsrRvfiCycleTrace.trace_refines
#print axioms LeanModels.Refine.CsrRvfiCycleTrace.append

end LeanModels.Refine
