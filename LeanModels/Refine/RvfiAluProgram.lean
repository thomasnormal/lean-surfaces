import LeanModels.Refine.RvfiRv32i

/-!
# Symbolic RVFI programs made only of RV32I ALU instructions

`AluInstruction` retains the fetched word, its decoded operation and operand
sources, and the decoder proof.  The folds below carry an arbitrary ALU-only
program through the stateful RV32I machine.  `AluRvfiTrace` is the proof-facing
certificate for a packed RVFI stream: invalid rows are bubbles and every
retiring row supplies the indexed ALU boundary for the next architectural
state.

This is the ALU-family counterpart of `RvfiAddiProgram`.  It is deliberately a
program certificate rather than a core model; a loaded-core invariant still
has to establish the indexed `Rv32iBoundary` at each retiring cycle.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## A decoded ALU program -/

/-- One decoded 32-bit ALU instruction, retaining the original word and its
decoder proof so a core-facing certificate cannot replace it with a guessed
encoding. -/
structure AluInstruction where
  word : Word
  op : AluOp
  rd : Reg
  src1 : Src1
  src2 : Src2
  decode : Fetched.decode (.word word) =
    some (.alu op rd src1 src2)

/-- The architectural input associated with one ALU instruction. -/
def aluProgramInput (memory : Memory) (instruction : AluInstruction) : Input :=
  { fetched := .word instruction.word, memory := memory, irq := 0 }

/-- The cycle/commit inputs for an ALU-only program.  ALU instructions do not
mutate data memory, so every instruction sees the same threaded memory. -/
def aluProgramInputs (memory : Memory) : List AluInstruction → List Input
  | [] => []
  | instruction :: program =>
      aluProgramInput memory instruction :: aluProgramInputs memory program

/-- The architectural state after executing an ALU-only program. -/
def aluProgramState (state : ArchState) : List AluInstruction → ArchState
  | [] => state
  | instruction :: program =>
      aluProgramState
        (aluNext state instruction.op instruction.rd instruction.src1
          instruction.src2) program

/-- The exact retirement stream for an ALU-only program. -/
def aluProgramRetirements (memory : Memory) (state : ArchState) :
    List AluInstruction → List Retirement
  | [] => []
  | instruction :: program =>
      aluRetirement state (aluProgramInput memory instruction)
          instruction.op instruction.rd instruction.src1 instruction.src2 ::
        aluProgramRetirements memory
          (aluNext state instruction.op instruction.rd instruction.src1
            instruction.src2) program

/-! ## Architectural folds -/

/-- An ALU write preserves the architectural x0 slot. -/
theorem aluNext_preserves_x0 (s : ArchState) (op : AluOp) (rd : Reg)
    (src1 : Src1) (src2 : Src2) :
    (aluNext s op rd src1 src2).readReg 0 = s.readReg 0 := by
  by_cases hrd : rd = 0
  · simp [aluNext, ArchState.readReg, ArchState.writeReg, hrd]
  · have h0rd : (0 : Reg) ≠ rd := by
      intro h
      exact hrd h.symm
    simp [aluNext, ArchState.readReg, ArchState.writeReg, hrd, h0rd]

/-- A well-formed architectural state remains well formed after an ALU step. -/
theorem aluNext_preserves_WF (s : ArchState) (op : AluOp) (rd : Reg)
    (src1 : Src1) (src2 : Src2) (hWF : s.WF) :
    (aluNext s op rd src1 src2).WF := by
  have hx0 := aluNext_preserves_x0 s op rd src1 src2
  simpa [ArchState.WF, ArchState.readReg] using hx0.trans hWF

theorem aluProgramState_preserves_WF (state : ArchState)
    (program : List AluInstruction) (hWF : state.WF) :
    (aluProgramState state program).WF := by
  induction program generalizing state with
  | nil => exact hWF
  | cons instruction program ih =>
      apply ih
      exact aluNext_preserves_WF state instruction.op instruction.rd
        instruction.src1 instruction.src2 hWF

/-- The input fold preserves list concatenation. -/
theorem aluProgramInputs_append (memory : Memory)
    (first second : List AluInstruction) :
    aluProgramInputs memory (first ++ second) =
      aluProgramInputs memory first ++ aluProgramInputs memory second := by
  induction first with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, aluProgramInputs, ih, List.cons_append]

/-- The architectural ALU fold resumes from the state reached by its prefix. -/
theorem aluProgramState_append (state : ArchState)
    (first second : List AluInstruction) :
    aluProgramState state (first ++ second) =
      aluProgramState (aluProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, aluProgramState]
      exact ih (state :=
        aluNext state instruction.op instruction.rd instruction.src1
          instruction.src2)

/-- The retirement fold carries the same architectural prefix boundary as the
state fold. -/
theorem aluProgramRetirements_append (memory : Memory) (state : ArchState)
    (first second : List AluInstruction) :
    aluProgramRetirements memory state (first ++ second) =
      aluProgramRetirements memory state first ++
        aluProgramRetirements memory (aluProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, aluProgramRetirements]
      rw [ih (state :=
        aluNext state instruction.op instruction.rd instruction.src1
          instruction.src2)]
      rfl

/-! ## Stateful ISA equations -/

/-- One decoded ALU instruction drives the exact stateful ISA transition with
no memory update. -/
theorem rvMemoryMachineWith_alu_step
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (instruction : AluInstruction) :
    (rvMemoryMachineWith profile).step
        { arch := state, memory := memory }
        (aluProgramInput memory instruction) =
      ({ arch := aluNext state instruction.op instruction.rd instruction.src1
          instruction.src2, memory := memory },
        aluRetirement state (aluProgramInput memory instruction)
          instruction.op instruction.rd instruction.src1 instruction.src2) := by
  simp only [rvMemoryMachineWith, aluProgramInput]
  rw [isaStepWith_alu profile state memory instruction.word instruction.op
    instruction.rd instruction.src1 instruction.src2 instruction.decode]
  rfl

/-- Threading the stateful ISA machine through every ALU instruction gives the
folded architectural state and unchanged memory. -/
theorem rvMemoryMachineWith_alu_program_state
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (program : List AluInstruction) :
    machineStateAfter (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (aluProgramInputs memory program) =
      { arch := aluProgramState state program, memory := memory } := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [aluProgramInputs, machineStateAfter]
      rw [rvMemoryMachineWith_alu_step profile state memory instruction]
      simpa [aluProgramState] using
        (ih (state := aluNext state instruction.op instruction.rd
          instruction.src1 instruction.src2))

/-- The same ALU program has exactly the retirement stream prescribed by its
architectural fold. -/
theorem rvMemoryMachineWith_alu_program_trace
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (program : List AluInstruction) :
    trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (aluProgramInputs memory program) =
      aluProgramRetirements memory state program := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [aluProgramInputs, trace, aluProgramRetirements]
      change
        ((rvMemoryMachineWith profile).step
            { arch := state, memory := memory }
            (aluProgramInput memory instruction)).2 ::
          trace (rvMemoryMachineWith profile)
            ((rvMemoryMachineWith profile).step
              { arch := state, memory := memory }
              (aluProgramInput memory instruction)).1
            (aluProgramInputs memory program) = _
      rw [rvMemoryMachineWith_alu_step profile state memory instruction]
      simpa using
        (ih (state := aluNext state instruction.op instruction.rd
          instruction.src1 instruction.src2))

/-- The stateful ALU machine resumes at the exact memory-machine state after
the first program segment. -/
theorem rvMemoryMachineWith_alu_program_state_append
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (first second : List AluInstruction) :
    machineStateAfter (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (aluProgramInputs memory (first ++ second)) =
      machineStateAfter (rvMemoryMachineWith profile)
        (machineStateAfter (rvMemoryMachineWith profile)
          { arch := state, memory := memory }
          (aluProgramInputs memory first))
        (aluProgramInputs memory second) := by
  rw [aluProgramInputs_append, machineStateAfter_append]

/-- The stateful ALU retirement stream splits at the same first-segment
boundary as the architectural state. -/
theorem rvMemoryMachineWith_alu_program_trace_append
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (first second : List AluInstruction) :
    trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (aluProgramInputs memory (first ++ second)) =
      trace (rvMemoryMachineWith profile)
          { arch := state, memory := memory }
          (aluProgramInputs memory first) ++
        trace (rvMemoryMachineWith profile)
          (machineStateAfter (rvMemoryMachineWith profile)
            { arch := state, memory := memory }
            (aluProgramInputs memory first))
          (aluProgramInputs memory second) := by
  rw [aluProgramInputs_append, machineTrace_append]

/-! ## Raw RVFI certificate for an arbitrary ALU program -/

/-- A raw RVFI stream whose retiring rows are exactly the supplied ALU
program. -/
inductive AluRvfiTrace (memory : Memory) :
    Nat → ArchState → List RvfiObservation → List AluInstruction → Prop where
  | nil (start : Nat) (state : ArchState) :
      AluRvfiTrace memory start state [] []
  | bubble {start : Nat} {state : ArchState}
      {observation : RvfiObservation} {observations : List RvfiObservation}
      {program : List AluInstruction}
      (hvalid : observation.valid = false)
      (tail : AluRvfiTrace memory start state observations program) :
      AluRvfiTrace memory start state (observation :: observations) program
  | retire {start : Nat} {state : ArchState}
      {observation : RvfiObservation}
      {observations : List RvfiObservation}
      {instruction : AluInstruction} {program : List AluInstruction}
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state (aluProgramInput memory instruction) observation
          { arch := aluNext state instruction.op instruction.rd instruction.src1
              instruction.src2,
            memory := memory }
          (aluRetirement state (aluProgramInput memory instruction)
            instruction.op instruction.rd instruction.src1 instruction.src2))
      (tail :
        AluRvfiTrace memory (start + 1)
          (aluNext state instruction.op instruction.rd instruction.src1
            instruction.src2)
          observations program) :
      AluRvfiTrace memory start state (observation :: observations)
        (instruction :: program)

/-- Every symbolic ALU certificate is an ordinary RVFI normalization
certificate. -/
theorem AluRvfiTrace.toRvfiTraceRefines
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List AluInstruction}
    (certificate : AluRvfiTrace memory start state observations program) :
    RvfiTraceRefines start observations
      (aluProgramRetirements memory state program) := by
  induction certificate with
  | nil start state => exact .nil start
  | bubble hvalid tail ih => exact .bubble hvalid ih
  | retire horder boundary tail ih =>
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      exact .retire hspec.1 horder hretirement ih

/-- The executable normalizer accepts exactly the retirement stream specified
by an arbitrary `AluRvfiTrace` certificate. -/
theorem AluRvfiTrace.normalize
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List AluInstruction}
    (certificate : AluRvfiTrace memory start state observations program) :
    normalizeRvfiTrace? start observations =
      some (aluProgramRetirements memory state program) :=
  (normalizeRvfiTrace?_iff).2 certificate.toRvfiTraceRefines

/-- The normalized symbolic ALU stream is the stateful ISA trace for the same
program. -/
theorem AluRvfiTrace.trace_refines
    (profile : PlatformProfile)
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List AluInstruction}
    (certificate : AluRvfiTrace memory start state observations program) :
    normalizeRvfiTrace? start observations =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (aluProgramInputs memory program)) := by
  calc
    normalizeRvfiTrace? start observations =
        some (aluProgramRetirements memory state program) :=
      certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (aluProgramInputs memory program)) := by
      rw [rvMemoryMachineWith_alu_program_trace]

/-! ## Composing raw ALU certificates -/

/-- Raw ALU certificates compose at the next retirement order and folded
architectural state produced by the first program chunk. -/
theorem AluRvfiTrace.append
    {memory : Memory} {start : Nat} {state : ArchState}
    {firstObservations secondObservations : List RvfiObservation}
    {firstProgram secondProgram : List AluInstruction}
    (first : AluRvfiTrace memory start state firstObservations firstProgram)
    (second : AluRvfiTrace memory
      (start + firstProgram.length)
      (aluProgramState state firstProgram)
      secondObservations secondProgram) :
    AluRvfiTrace memory start state
      (firstObservations ++ secondObservations)
      (firstProgram ++ secondProgram) := by
  induction first with
  | nil start state =>
      simpa [aluProgramState] using second
  | bubble hvalid tail ih =>
      refine AluRvfiTrace.bubble hvalid ?_
      apply ih
      simpa [aluProgramState] using second
  | retire horder boundary tail ih =>
      refine AluRvfiTrace.retire horder boundary ?_
      apply ih
      simpa [aluProgramState, List.length_cons, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using second

/-! ## Input-aware cycle certificate -/

/-- The ALU invariant tied to an actual packed-RVFI cycle machine.  Bubble
cycles may carry any input; a retiring cycle must present the exact ALU input
whose memory view it reports. -/
inductive AluRvfiCycleTrace {State : Type}
    (machine : RvfiCycleMachine State) (memory : Memory) :
    Nat → State → ArchState → List Input → List AluInstruction → Prop where
  | nil (start : Nat) (coreState : State) (state : ArchState) :
      AluRvfiCycleTrace machine memory start coreState state [] []
  | bubble {start : Nat} {coreState coreState' : State}
      {state : ArchState} {cycleInput : Input} {cycles : List Input}
      {program : List AluInstruction} {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hvalid : observation.valid = false)
      (tail : AluRvfiCycleTrace machine memory start coreState' state
        cycles program) :
      AluRvfiCycleTrace machine memory start coreState state
        (cycleInput :: cycles) program
  | retire {start : Nat} {coreState coreState' : State}
      {state : ArchState} {cycleInput : Input} {cycles : List Input}
      {instruction : AluInstruction} {program : List AluInstruction}
      {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hinput : cycleInput = aluProgramInput memory instruction)
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state (aluProgramInput memory instruction) observation
          { arch := aluNext state instruction.op instruction.rd instruction.src1
              instruction.src2,
            memory := memory }
          (aluRetirement state (aluProgramInput memory instruction)
            instruction.op instruction.rd instruction.src1 instruction.src2))
      (tail : AluRvfiCycleTrace machine memory (start + 1) coreState'
        (aluNext state instruction.op instruction.rd instruction.src1
          instruction.src2)
        cycles program) :
      AluRvfiCycleTrace machine memory start coreState state
        (cycleInput :: cycles) (instruction :: program)

/-- An input-aware ALU certificate normalizes the observations emitted by its
actual cycle machine to the symbolic program's retirement stream. -/
theorem AluRvfiCycleTrace.normalize
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List AluInstruction}
    (certificate : AluRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (aluProgramRetirements memory state program) := by
  induction certificate with
  | nil start coreState state => rfl
  | bubble hstep hvalid tail ih =>
      simp only [rvfiObservations, hstep]
      simp [normalizeRvfiTrace?, hvalid, ih]
  | retire hstep hinput horder boundary tail ih =>
      simp only [rvfiObservations, hstep]
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      simp [normalizeRvfiTrace?, aluProgramRetirements, hspec.1,
        horder, hretirement, ih]

/-- The cycle inputs retained by an input-aware ALU certificate are exactly
the symbolic program inputs; bubbles are removed by the optional adapter. -/
theorem AluRvfiCycleTrace.retireInputs_eq
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List AluInstruction}
    (certificate : AluRvfiCycleTrace machine memory start coreState state
      cycles program) :
    retireInputs machine.toCycleMachine coreState cycles =
      aluProgramInputs memory program := by
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
            (coreState', some (aluRetirement state
              (aluProgramInput memory instruction)
              instruction.op instruction.rd instruction.src1 instruction.src2)) := by
        simp [RvfiCycleMachine.toCycleMachine, hstep, hretirement]
      simp only [retireInputs, hstep']
      rw [hinput]
      simpa [aluProgramInputs] using ih

/-- Direct core-stream theorem: an input-aware ALU certificate relates the
normalized packed observations to the stateful ISA trace on the machine's own
retiring inputs. -/
theorem AluRvfiCycleTrace.trace_refines
    {State : Type} (profile : PlatformProfile)
    {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List AluInstruction}
    (certificate : AluRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
  calc
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
        some (aluProgramRetirements memory state program) :=
      certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (aluProgramInputs memory program)) := by
      rw [rvMemoryMachineWith_alu_program_trace]
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
      rw [certificate.retireInputs_eq]

/-! ## Composing input-aware cycle certificates -/

/-- Input-aware ALU certificates compose at the exact state and retirement
order boundary produced by the first program chunk. -/
theorem AluRvfiCycleTrace.append
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {firstCycles secondCycles : List Input}
    {firstProgram secondProgram : List AluInstruction}
    (first : AluRvfiCycleTrace machine memory start coreState state
      firstCycles firstProgram)
    (second : AluRvfiCycleTrace machine memory
      (start + firstProgram.length)
      (rvfiStateAfter machine coreState firstCycles)
      (aluProgramState state firstProgram)
      secondCycles secondProgram) :
    AluRvfiCycleTrace machine memory start coreState state
      (firstCycles ++ secondCycles) (firstProgram ++ secondProgram) := by
  induction first with
  | nil start coreState state =>
      simpa [rvfiStateAfter, aluProgramState] using second
  | bubble hstep hvalid tail ih =>
      refine AluRvfiCycleTrace.bubble hstep hvalid ?_
      apply ih
      simpa [rvfiStateAfter, hstep] using second
  | retire hstep hinput horder boundary tail ih =>
      refine AluRvfiCycleTrace.retire hstep hinput horder boundary ?_
      apply ih
      simpa [rvfiStateAfter, aluProgramState, hstep, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using second

#print axioms LeanModels.Refine.aluNext_preserves_x0
#print axioms LeanModels.Refine.aluNext_preserves_WF
#print axioms LeanModels.Refine.aluProgramState_preserves_WF
#print axioms LeanModels.Refine.aluProgramInputs_append
#print axioms LeanModels.Refine.aluProgramState_append
#print axioms LeanModels.Refine.aluProgramRetirements_append
#print axioms LeanModels.Refine.rvMemoryMachineWith_alu_step
#print axioms LeanModels.Refine.rvMemoryMachineWith_alu_program_state
#print axioms LeanModels.Refine.rvMemoryMachineWith_alu_program_trace
#print axioms LeanModels.Refine.rvMemoryMachineWith_alu_program_state_append
#print axioms LeanModels.Refine.rvMemoryMachineWith_alu_program_trace_append
#print axioms LeanModels.Refine.AluRvfiTrace.toRvfiTraceRefines
#print axioms LeanModels.Refine.AluRvfiTrace.normalize
#print axioms LeanModels.Refine.AluRvfiTrace.trace_refines
#print axioms LeanModels.Refine.AluRvfiTrace.append
#print axioms LeanModels.Refine.AluRvfiCycleTrace.normalize
#print axioms LeanModels.Refine.AluRvfiCycleTrace.retireInputs_eq
#print axioms LeanModels.Refine.AluRvfiCycleTrace.trace_refines
#print axioms LeanModels.Refine.AluRvfiCycleTrace.append

end LeanModels.Refine
