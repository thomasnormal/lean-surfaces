import LeanModels.Refine.RvfiRv32i

/-!
# Symbolic RVFI programs made only of RV32I conditional branches

`BranchInstruction` retains the fetched word, its decoded condition, two
register sources, offset, and decoder proof.  The folds below carry an arbitrary conditional-branch
program through the stateful RV32I machine.  `BranchRvfiTrace` is the proof-facing
certificate for a packed RVFI stream: invalid rows are bubbles and every
retiring row supplies the indexed branch boundary for the next architectural
state.

This is the branch-family counterpart of `RvfiAddiProgram`.  It is deliberately a
program certificate rather than a core model; a loaded-core invariant still
has to establish the indexed `Rv32iBoundary` at each retiring cycle.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## A decoded conditional-branch program -/

/-- One decoded 32-bit conditional-branch instruction, retaining the original word,
condition, source registers, offset, and decoder proof so a core-facing
certificate cannot replace it with a guessed encoding. -/
structure BranchInstruction where
  word : Word
  cond : BranchCond
  rs1 : Reg
  rs2 : Reg
  offset : Word
  decode : Fetched.decode (.word word) =
    some (.branch cond rs1 rs2 offset)

/-- The architectural input associated with one conditional-branch instruction. -/
def branchProgramInput (memory : Memory) (instruction : BranchInstruction) : Input :=
  { fetched := .word instruction.word, memory := memory, irq := 0 }

/-- The cycle/commit inputs for a conditional-branch program.  Branch instructions do not
mutate data memory, so every instruction sees the same threaded memory. -/
def branchProgramInputs (memory : Memory) : List BranchInstruction → List Input
  | [] => []
  | instruction :: program =>
      branchProgramInput memory instruction :: branchProgramInputs memory program

/-- The architectural state after executing a conditional-branch program. -/
def branchProgramState (state : ArchState) : List BranchInstruction → ArchState
  | [] => state
  | instruction :: program =>
      branchProgramState
        (branchNext state instruction.cond instruction.rs1 instruction.rs2
          instruction.offset) program

/-- The exact retirement stream for a conditional-branch program. -/
def branchProgramRetirements (memory : Memory) (state : ArchState) :
    List BranchInstruction → List Retirement
  | [] => []
  | instruction :: program =>
      branchRetirement state (branchProgramInput memory instruction)
          instruction.cond instruction.rs1 instruction.rs2 instruction.offset ::
        branchProgramRetirements memory
          (branchNext state instruction.cond instruction.rs1 instruction.rs2
            instruction.offset) program

/-! ## Program-fold composition -/

/-- The input fold preserves list concatenation. -/
theorem branchProgramInputs_append (memory : Memory)
    (first second : List BranchInstruction) :
    branchProgramInputs memory (first ++ second) =
      branchProgramInputs memory first ++ branchProgramInputs memory second := by
  induction first with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, branchProgramInputs, ih, List.cons_append]

/-- The architectural branch fold resumes from the state reached by its prefix. -/
theorem branchProgramState_append (state : ArchState)
    (first second : List BranchInstruction) :
    branchProgramState state (first ++ second) =
      branchProgramState (branchProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, branchProgramState]
      exact ih (state :=
        branchNext state instruction.cond instruction.rs1 instruction.rs2
          instruction.offset)

/-- The retirement fold carries the same architectural prefix boundary as the
state fold. -/
theorem branchProgramRetirements_append (memory : Memory) (state : ArchState)
    (first second : List BranchInstruction) :
    branchProgramRetirements memory state (first ++ second) =
      branchProgramRetirements memory state first ++
        branchProgramRetirements memory (branchProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, branchProgramRetirements]
      rw [ih (state :=
        branchNext state instruction.cond instruction.rs1 instruction.rs2
          instruction.offset)]
      rfl

/-! ## Stateful ISA equations -/

/-- One decoded branch instruction drives the exact stateful ISA transition with
no memory update. -/
theorem rvMemoryMachineWith_branch_step
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (instruction : BranchInstruction) :
    (rvMemoryMachineWith profile).step
        { arch := state, memory := memory }
        (branchProgramInput memory instruction) =
      ({ arch := branchNext state instruction.cond instruction.rs1 instruction.rs2
          instruction.offset, memory := memory },
        branchRetirement state (branchProgramInput memory instruction)
          instruction.cond instruction.rs1 instruction.rs2 instruction.offset) := by
  simp only [rvMemoryMachineWith, branchProgramInput]
  rw [isaStepWith_branch profile state memory instruction.word instruction.cond
    instruction.rs1 instruction.rs2 instruction.offset instruction.decode]
  rfl

/-- Threading the stateful ISA machine through every conditional branch gives the
folded architectural state and unchanged memory. -/
theorem rvMemoryMachineWith_branch_program_state
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (program : List BranchInstruction) :
    machineStateAfter (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (branchProgramInputs memory program) =
      { arch := branchProgramState state program, memory := memory } := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [branchProgramInputs, machineStateAfter]
      rw [rvMemoryMachineWith_branch_step profile state memory instruction]
      simpa [branchProgramState] using
        (ih (state := branchNext state instruction.cond instruction.rs1
          instruction.rs2 instruction.offset))

/-- The same branch program has exactly the retirement stream prescribed by its
architectural fold. -/
theorem rvMemoryMachineWith_branch_program_trace
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (program : List BranchInstruction) :
    trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (branchProgramInputs memory program) =
      branchProgramRetirements memory state program := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [branchProgramInputs, trace, branchProgramRetirements]
      change
        ((rvMemoryMachineWith profile).step
            { arch := state, memory := memory }
            (branchProgramInput memory instruction)).2 ::
          trace (rvMemoryMachineWith profile)
            ((rvMemoryMachineWith profile).step
              { arch := state, memory := memory }
              (branchProgramInput memory instruction)).1
            (branchProgramInputs memory program) = _
      rw [rvMemoryMachineWith_branch_step profile state memory instruction]
      simpa using
        (ih (state := branchNext state instruction.cond instruction.rs1
          instruction.rs2 instruction.offset))

/-- The stateful branch machine resumes at the exact memory-machine state after
the first program segment. -/
theorem rvMemoryMachineWith_branch_program_state_append
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (first second : List BranchInstruction) :
    machineStateAfter (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (branchProgramInputs memory (first ++ second)) =
      machineStateAfter (rvMemoryMachineWith profile)
        (machineStateAfter (rvMemoryMachineWith profile)
          { arch := state, memory := memory }
          (branchProgramInputs memory first))
        (branchProgramInputs memory second) := by
  rw [branchProgramInputs_append, machineStateAfter_append]

/-- The stateful conditional-branch retirement stream splits at the same first-segment
boundary as the architectural state. -/
theorem rvMemoryMachineWith_branch_program_trace_append
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (first second : List BranchInstruction) :
    trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (branchProgramInputs memory (first ++ second)) =
      trace (rvMemoryMachineWith profile)
          { arch := state, memory := memory }
          (branchProgramInputs memory first) ++
        trace (rvMemoryMachineWith profile)
          (machineStateAfter (rvMemoryMachineWith profile)
            { arch := state, memory := memory }
            (branchProgramInputs memory first))
          (branchProgramInputs memory second) := by
  rw [branchProgramInputs_append, machineTrace_append]

/-! ## Raw RVFI certificate for an arbitrary conditional-branch program -/

/-- A raw RVFI stream whose retiring rows are exactly the supplied conditional-branch
program. -/
inductive BranchRvfiTrace (memory : Memory) :
    Nat → ArchState → List RvfiObservation → List BranchInstruction → Prop where
  | nil (start : Nat) (state : ArchState) :
      BranchRvfiTrace memory start state [] []
  | bubble {start : Nat} {state : ArchState}
      {observation : RvfiObservation} {observations : List RvfiObservation}
      {program : List BranchInstruction}
      (hvalid : observation.valid = false)
      (tail : BranchRvfiTrace memory start state observations program) :
      BranchRvfiTrace memory start state (observation :: observations) program
  | retire {start : Nat} {state : ArchState}
      {observation : RvfiObservation}
      {observations : List RvfiObservation}
      {instruction : BranchInstruction} {program : List BranchInstruction}
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state (branchProgramInput memory instruction) observation
          { arch := branchNext state instruction.cond instruction.rs1 instruction.rs2
              instruction.offset,
            memory := memory }
          (branchRetirement state (branchProgramInput memory instruction)
            instruction.cond instruction.rs1 instruction.rs2 instruction.offset))
      (tail :
        BranchRvfiTrace memory (start + 1)
          (branchNext state instruction.cond instruction.rs1 instruction.rs2
            instruction.offset)
          observations program) :
      BranchRvfiTrace memory start state (observation :: observations)
        (instruction :: program)

/-- Every symbolic branch certificate is an ordinary RVFI normalization
certificate. -/
theorem BranchRvfiTrace.toRvfiTraceRefines
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List BranchInstruction}
    (certificate : BranchRvfiTrace memory start state observations program) :
    RvfiTraceRefines start observations
      (branchProgramRetirements memory state program) := by
  induction certificate with
  | nil start state => exact .nil start
  | bubble hvalid tail ih => exact .bubble hvalid ih
  | retire horder boundary tail ih =>
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      exact .retire hspec.1 horder hretirement ih

/-- The executable normalizer accepts exactly the retirement stream specified
by an arbitrary `BranchRvfiTrace` certificate. -/
theorem BranchRvfiTrace.normalize
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List BranchInstruction}
    (certificate : BranchRvfiTrace memory start state observations program) :
    normalizeRvfiTrace? start observations =
      some (branchProgramRetirements memory state program) :=
  (normalizeRvfiTrace?_iff).2 certificate.toRvfiTraceRefines

/-- The normalized symbolic branch stream is the stateful ISA trace for the same
program. -/
theorem BranchRvfiTrace.trace_refines
    (profile : PlatformProfile)
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List BranchInstruction}
    (certificate : BranchRvfiTrace memory start state observations program) :
    normalizeRvfiTrace? start observations =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (branchProgramInputs memory program)) := by
  calc
    normalizeRvfiTrace? start observations =
        some (branchProgramRetirements memory state program) :=
      certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (branchProgramInputs memory program)) := by
      rw [rvMemoryMachineWith_branch_program_trace]

/-! ## Composing raw branch certificates -/

/-- Raw branch certificates compose at the next retirement order and folded
architectural state produced by the first program chunk. -/
theorem BranchRvfiTrace.append
    {memory : Memory} {start : Nat} {state : ArchState}
    {firstObservations secondObservations : List RvfiObservation}
    {firstProgram secondProgram : List BranchInstruction}
    (first : BranchRvfiTrace memory start state firstObservations firstProgram)
    (second : BranchRvfiTrace memory
      (start + firstProgram.length)
      (branchProgramState state firstProgram)
      secondObservations secondProgram) :
    BranchRvfiTrace memory start state
      (firstObservations ++ secondObservations)
      (firstProgram ++ secondProgram) := by
  induction first with
  | nil start state =>
      simpa [branchProgramState] using second
  | bubble hvalid tail ih =>
      refine BranchRvfiTrace.bubble hvalid ?_
      apply ih
      simpa [branchProgramState] using second
  | retire horder boundary tail ih =>
      refine BranchRvfiTrace.retire horder boundary ?_
      apply ih
      simpa [branchProgramState, List.length_cons, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using second

/-! ## Input-aware cycle certificate -/

/-- The branch invariant tied to an actual packed-RVFI cycle machine.  Bubble
cycles may carry any input; a retiring cycle must present the exact branch input
whose memory view it reports. -/
inductive BranchRvfiCycleTrace {State : Type}
    (machine : RvfiCycleMachine State) (memory : Memory) :
    Nat → State → ArchState → List Input → List BranchInstruction → Prop where
  | nil (start : Nat) (coreState : State) (state : ArchState) :
      BranchRvfiCycleTrace machine memory start coreState state [] []
  | bubble {start : Nat} {coreState coreState' : State}
      {state : ArchState} {cycleInput : Input} {cycles : List Input}
      {program : List BranchInstruction} {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hvalid : observation.valid = false)
      (tail : BranchRvfiCycleTrace machine memory start coreState' state
        cycles program) :
      BranchRvfiCycleTrace machine memory start coreState state
        (cycleInput :: cycles) program
  | retire {start : Nat} {coreState coreState' : State}
      {state : ArchState} {cycleInput : Input} {cycles : List Input}
      {instruction : BranchInstruction} {program : List BranchInstruction}
      {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hinput : cycleInput = branchProgramInput memory instruction)
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state (branchProgramInput memory instruction) observation
          { arch := branchNext state instruction.cond instruction.rs1 instruction.rs2
              instruction.offset,
            memory := memory }
          (branchRetirement state (branchProgramInput memory instruction)
            instruction.cond instruction.rs1 instruction.rs2 instruction.offset))
      (tail : BranchRvfiCycleTrace machine memory (start + 1) coreState'
        (branchNext state instruction.cond instruction.rs1 instruction.rs2
          instruction.offset)
        cycles program) :
      BranchRvfiCycleTrace machine memory start coreState state
        (cycleInput :: cycles) (instruction :: program)

/-- An input-aware branch certificate normalizes the observations emitted by its
actual cycle machine to the symbolic program's retirement stream. -/
theorem BranchRvfiCycleTrace.normalize
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List BranchInstruction}
    (certificate : BranchRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (branchProgramRetirements memory state program) := by
  induction certificate with
  | nil start coreState state => rfl
  | bubble hstep hvalid tail ih =>
      simp only [rvfiObservations, hstep]
      simp [normalizeRvfiTrace?, hvalid, ih]
  | retire hstep hinput horder boundary tail ih =>
      simp only [rvfiObservations, hstep]
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      simp [normalizeRvfiTrace?, branchProgramRetirements, hspec.1,
        horder, hretirement, ih]

/-- The cycle inputs retained by an input-aware branch certificate are exactly
the symbolic program inputs; bubbles are removed by the optional adapter. -/
theorem BranchRvfiCycleTrace.retireInputs_eq
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List BranchInstruction}
    (certificate : BranchRvfiCycleTrace machine memory start coreState state
      cycles program) :
    retireInputs machine.toCycleMachine coreState cycles =
      branchProgramInputs memory program := by
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
            (coreState', some (branchRetirement state
              (branchProgramInput memory instruction)
              instruction.cond instruction.rs1 instruction.rs2 instruction.offset)) := by
        simp [RvfiCycleMachine.toCycleMachine, hstep, hretirement]
      simp only [retireInputs, hstep']
      rw [hinput]
      simpa [branchProgramInputs] using ih

/-- Direct core-stream theorem: an input-aware branch certificate relates the
normalized packed observations to the stateful ISA trace on the machine's own
retiring inputs. -/
theorem BranchRvfiCycleTrace.trace_refines
    {State : Type} (profile : PlatformProfile)
    {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List BranchInstruction}
    (certificate : BranchRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
  calc
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
        some (branchProgramRetirements memory state program) :=
      certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (branchProgramInputs memory program)) := by
      rw [rvMemoryMachineWith_branch_program_trace]
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
      rw [certificate.retireInputs_eq]

/-! ## Composing input-aware cycle certificates -/

/-- Input-aware branch certificates compose at the exact state and retirement
order boundary produced by the first program chunk. -/
theorem BranchRvfiCycleTrace.append
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {firstCycles secondCycles : List Input}
    {firstProgram secondProgram : List BranchInstruction}
    (first : BranchRvfiCycleTrace machine memory start coreState state
      firstCycles firstProgram)
    (second : BranchRvfiCycleTrace machine memory
      (start + firstProgram.length)
      (rvfiStateAfter machine coreState firstCycles)
      (branchProgramState state firstProgram)
      secondCycles secondProgram) :
    BranchRvfiCycleTrace machine memory start coreState state
      (firstCycles ++ secondCycles) (firstProgram ++ secondProgram) := by
  induction first with
  | nil start coreState state =>
      simpa [rvfiStateAfter, branchProgramState] using second
  | bubble hstep hvalid tail ih =>
      refine BranchRvfiCycleTrace.bubble hstep hvalid ?_
      apply ih
      simpa [rvfiStateAfter, hstep] using second
  | retire hstep hinput horder boundary tail ih =>
      refine BranchRvfiCycleTrace.retire hstep hinput horder boundary ?_
      apply ih
      simpa [rvfiStateAfter, branchProgramState, hstep, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using second

#print axioms LeanModels.Refine.branchProgramInputs_append
#print axioms LeanModels.Refine.branchProgramState_append
#print axioms LeanModels.Refine.branchProgramRetirements_append
#print axioms LeanModels.Refine.rvMemoryMachineWith_branch_step
#print axioms LeanModels.Refine.rvMemoryMachineWith_branch_program_state
#print axioms LeanModels.Refine.rvMemoryMachineWith_branch_program_trace
#print axioms LeanModels.Refine.rvMemoryMachineWith_branch_program_state_append
#print axioms LeanModels.Refine.rvMemoryMachineWith_branch_program_trace_append
#print axioms LeanModels.Refine.BranchRvfiTrace.toRvfiTraceRefines
#print axioms LeanModels.Refine.BranchRvfiTrace.normalize
#print axioms LeanModels.Refine.BranchRvfiTrace.trace_refines
#print axioms LeanModels.Refine.BranchRvfiTrace.append
#print axioms LeanModels.Refine.BranchRvfiCycleTrace.normalize
#print axioms LeanModels.Refine.BranchRvfiCycleTrace.retireInputs_eq
#print axioms LeanModels.Refine.BranchRvfiCycleTrace.trace_refines
#print axioms LeanModels.Refine.BranchRvfiCycleTrace.append

end LeanModels.Refine
