import LeanModels.Refine.RvfiMemAll
import LeanModels.Refine.RvfiRv32i

/-!
# Symbolic RVFI programs made only of RV32I memory instructions

`MemInstruction` retains a fetched word, its generic load/store shape, and the
decoder proof.  The folds below thread both architectural registers and byte
memory, so a later loaded-core certificate can cover arbitrary mixtures of
loads and stores without replacing the existing RV32I memory semantics.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## A decoded memory program -/

/-- One decoded RV32I memory instruction, retaining the exact operation shape
and its parser-derived decoder proof. -/
structure MemInstruction where
  word : Word
  kind : MemOp
  r : Reg
  rs1 : Reg
  imm : Word
  decode : Fetched.decode (.word word) =
    some (kind.toInstr r rs1 imm)

/-- The input associated with one memory instruction at a threaded state. -/
def memProgramInput (state : RvMemoryState) (instruction : MemInstruction) :
    Input :=
  { fetched := .word instruction.word, memory := state.memory, irq := 0 }

/-- The stateful architectural transition represented by one memory
instruction. -/
def memProgramStep (state : RvMemoryState) (instruction : MemInstruction) :
    RvMemoryState :=
  { arch := memNext state.arch state.memory instruction.kind instruction.r
      instruction.rs1 instruction.imm
    memory := memAfter state.memory state.arch instruction.kind instruction.r
      instruction.rs1 instruction.imm }

/-- The cycle inputs for a memory-only program, with each input seeing the
memory produced by its preceding prefix. -/
def memProgramInputs : RvMemoryState → List MemInstruction → List Input
  | _, [] => []
  | state, instruction :: program =>
      memProgramInput state instruction ::
        memProgramInputs (memProgramStep state instruction) program

/-- The threaded architectural state after a memory-only program. -/
def memProgramState : RvMemoryState → List MemInstruction → RvMemoryState
  | state, [] => state
  | state, instruction :: program =>
      memProgramState (memProgramStep state instruction) program

/-- The exact retirement stream for a memory-only program. -/
def memProgramRetirements : RvMemoryState → List MemInstruction →
    List Retirement
  | _, [] => []
  | state, instruction :: program =>
      memRetirement state.arch (memProgramInput state instruction)
          instruction.kind instruction.r instruction.rs1 instruction.imm ::
        memProgramRetirements (memProgramStep state instruction) program

/-! ## Program folds -/

/-- The input fold resumes from the state reached by its prefix. -/
theorem memProgramInputs_append (state : RvMemoryState)
    (first second : List MemInstruction) :
    memProgramInputs state (first ++ second) =
      memProgramInputs state first ++
        memProgramInputs (memProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, memProgramInputs, memProgramState]
      simp [ih (state := memProgramStep state instruction)]

/-- The state fold resumes from the state reached by its prefix. -/
theorem memProgramState_append (state : RvMemoryState)
    (first second : List MemInstruction) :
    memProgramState state (first ++ second) =
      memProgramState (memProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, memProgramState]
      exact ih (state := memProgramStep state instruction)

/-- The retirement fold carries the same threaded state boundary as the
state fold. -/
theorem memProgramRetirements_append (state : RvMemoryState)
    (first second : List MemInstruction) :
    memProgramRetirements state (first ++ second) =
      memProgramRetirements state first ++
        memProgramRetirements (memProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, memProgramRetirements]
      rw [ih (state := memProgramStep state instruction)]
      rfl

/-! ## Stateful ISA equations -/

/-- One decoded memory instruction drives the exact stateful ISA transition. -/
theorem rvMemoryMachineWith_mem_step
    (profile : PlatformProfile) (state : RvMemoryState)
    (instruction : MemInstruction) :
    (rvMemoryMachineWith profile).step state
        (memProgramInput state instruction) =
      (memProgramStep state instruction,
        memRetirement state.arch (memProgramInput state instruction)
          instruction.kind instruction.r instruction.rs1 instruction.imm) := by
  simp only [rvMemoryMachineWith, memProgramInput, memProgramStep]
  rw [isaStepWith_mem profile state.arch state.memory instruction.word
    instruction.kind instruction.r instruction.rs1 instruction.imm
    instruction.decode]
  cases instruction.kind <;> rfl

/-- Threading the stateful ISA machine through every memory instruction gives
the folded architectural and byte-memory state. -/
theorem rvMemoryMachineWith_mem_program_state
    (profile : PlatformProfile) (state : RvMemoryState)
    (program : List MemInstruction) :
    machineStateAfter (rvMemoryMachineWith profile) state
        (memProgramInputs state program) =
      memProgramState state program := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [memProgramInputs, machineStateAfter]
      rw [rvMemoryMachineWith_mem_step profile state instruction]
      simpa [memProgramState] using
        (ih (state := memProgramStep state instruction))

/-- The stateful memory machine emits exactly the retirement fold for the
same memory program. -/
theorem rvMemoryMachineWith_mem_program_trace
    (profile : PlatformProfile) (state : RvMemoryState)
    (program : List MemInstruction) :
    trace (rvMemoryMachineWith profile) state
        (memProgramInputs state program) =
      memProgramRetirements state program := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [memProgramInputs, trace, memProgramRetirements]
      change
        ((rvMemoryMachineWith profile).step state
            (memProgramInput state instruction)).2 ::
          trace (rvMemoryMachineWith profile)
            ((rvMemoryMachineWith profile).step state
              (memProgramInput state instruction)).1
            (memProgramInputs (memProgramStep state instruction) program) = _
      rw [rvMemoryMachineWith_mem_step profile state instruction]
      simpa using
        (ih (state := memProgramStep state instruction))

/-! ## Append bridges at the stateful machine -/

/-- The stateful memory machine resumes at the exact state after a prefix. -/
theorem rvMemoryMachineWith_mem_program_state_append
    (profile : PlatformProfile) (state : RvMemoryState)
    (first second : List MemInstruction) :
    machineStateAfter (rvMemoryMachineWith profile) state
        (memProgramInputs state (first ++ second)) =
      machineStateAfter (rvMemoryMachineWith profile)
        (machineStateAfter (rvMemoryMachineWith profile) state
          (memProgramInputs state first))
        (memProgramInputs (memProgramState state first) second) := by
  rw [memProgramInputs_append, machineStateAfter_append]

/-- The stateful memory retirement stream splits at the same prefix state. -/
theorem rvMemoryMachineWith_mem_program_trace_append
    (profile : PlatformProfile) (state : RvMemoryState)
    (first second : List MemInstruction) :
    trace (rvMemoryMachineWith profile) state
        (memProgramInputs state (first ++ second)) =
      trace (rvMemoryMachineWith profile) state
          (memProgramInputs state first) ++
        trace (rvMemoryMachineWith profile)
          (machineStateAfter (rvMemoryMachineWith profile) state
            (memProgramInputs state first))
          (memProgramInputs (memProgramState state first) second) := by
  rw [memProgramInputs_append, machineTrace_append]

/-! ## Raw RVFI certificate for an arbitrary memory program -/

/-- A raw RVFI stream whose retiring rows are exactly the supplied threaded
load/store program. -/
inductive MemRvfiTrace :
    Nat → RvMemoryState → List RvfiObservation → List MemInstruction → Prop
  where
  | nil (start : Nat) (state : RvMemoryState) :
      MemRvfiTrace start state [] []
  | bubble {start : Nat} {state : RvMemoryState}
      {observation : RvfiObservation} {observations : List RvfiObservation}
      {program : List MemInstruction}
      (hvalid : observation.valid = false)
      (tail : MemRvfiTrace start state observations program) :
      MemRvfiTrace start state (observation :: observations) program
  | retire {start : Nat} {state : RvMemoryState}
      {observation : RvfiObservation}
      {observations : List RvfiObservation}
      {instruction : MemInstruction} {program : List MemInstruction}
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state.arch (memProgramInput state instruction)
          observation (memProgramStep state instruction)
          (memRetirement state.arch (memProgramInput state instruction)
            instruction.kind instruction.r instruction.rs1 instruction.imm))
      (tail :
        MemRvfiTrace (start + 1) (memProgramStep state instruction)
          observations program) :
      MemRvfiTrace start state (observation :: observations)
        (instruction :: program)

/-- Every symbolic memory certificate is an ordinary RVFI normalization
certificate. -/
theorem MemRvfiTrace.toRvfiTraceRefines
    {start : Nat} {state : RvMemoryState}
    {observations : List RvfiObservation} {program : List MemInstruction}
    (certificate : MemRvfiTrace start state observations program) :
    RvfiTraceRefines start observations
      (memProgramRetirements state program) := by
  induction certificate with
  | nil start state => exact .nil start
  | bubble hvalid tail ih => exact .bubble hvalid ih
  | retire horder boundary tail ih =>
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      exact .retire hspec.1 horder hretirement ih

/-- The executable normalizer accepts exactly the retirement stream specified
by an arbitrary `MemRvfiTrace` certificate. -/
theorem MemRvfiTrace.normalize
    {start : Nat} {state : RvMemoryState}
    {observations : List RvfiObservation} {program : List MemInstruction}
    (certificate : MemRvfiTrace start state observations program) :
    normalizeRvfiTrace? start observations =
      some (memProgramRetirements state program) :=
  (normalizeRvfiTrace?_iff).2 certificate.toRvfiTraceRefines

/-- The normalized symbolic memory stream is the stateful ISA trace for the
same threaded load/store program. -/
theorem MemRvfiTrace.trace_refines
    (profile : PlatformProfile)
    {start : Nat} {state : RvMemoryState}
    {observations : List RvfiObservation} {program : List MemInstruction}
    (certificate : MemRvfiTrace start state observations program) :
    normalizeRvfiTrace? start observations =
      some (trace (rvMemoryMachineWith profile) state
        (memProgramInputs state program)) := by
  calc
    normalizeRvfiTrace? start observations =
        some (memProgramRetirements state program) :=
      certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile) state
        (memProgramInputs state program)) := by
      rw [rvMemoryMachineWith_mem_program_trace]

/-! ## Composing raw memory certificates -/

/-- Raw memory certificates compose at the next retirement order and the
threaded architectural/byte-memory state produced by the first program
chunk. -/
theorem MemRvfiTrace.append
    {start : Nat} {state : RvMemoryState}
    {firstObservations secondObservations : List RvfiObservation}
    {firstProgram secondProgram : List MemInstruction}
    (first : MemRvfiTrace start state firstObservations firstProgram)
    (second : MemRvfiTrace
      (start + firstProgram.length)
      (memProgramState state firstProgram)
      secondObservations secondProgram) :
    MemRvfiTrace start state
      (firstObservations ++ secondObservations)
      (firstProgram ++ secondProgram) := by
  induction first with
  | nil start state =>
      simpa [memProgramState] using second
  | bubble hvalid tail ih =>
      refine MemRvfiTrace.bubble hvalid ?_
      apply ih
      simpa [memProgramState] using second
  | retire horder boundary tail ih =>
      refine MemRvfiTrace.retire horder boundary ?_
      apply ih
      simpa [memProgramState, List.length_cons, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using second

#print axioms LeanModels.Refine.memProgramInputs_append
#print axioms LeanModels.Refine.memProgramState_append
#print axioms LeanModels.Refine.memProgramRetirements_append
#print axioms LeanModels.Refine.rvMemoryMachineWith_mem_step
#print axioms LeanModels.Refine.rvMemoryMachineWith_mem_program_state
#print axioms LeanModels.Refine.rvMemoryMachineWith_mem_program_trace
#print axioms LeanModels.Refine.rvMemoryMachineWith_mem_program_state_append
#print axioms LeanModels.Refine.rvMemoryMachineWith_mem_program_trace_append
#print axioms LeanModels.Refine.MemRvfiTrace.toRvfiTraceRefines
#print axioms LeanModels.Refine.MemRvfiTrace.normalize
#print axioms LeanModels.Refine.MemRvfiTrace.trace_refines
#print axioms LeanModels.Refine.MemRvfiTrace.append

end LeanModels.Refine
