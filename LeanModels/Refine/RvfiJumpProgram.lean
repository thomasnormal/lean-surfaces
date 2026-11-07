import LeanModels.Refine.RvfiRv32i
import LeanModels.Refine.Rv32iJump

/-!
# Symbolic RVFI programs made only of RV32I jumps

`JumpInstruction` retains the fetched word, semantic JAL/JALR kind, and decoder proof.
The folds below carry an arbitrary jump program through the stateful RV32I machine.  `JumpRvfiTrace` is the proof-facing
certificate for a packed RVFI stream: invalid rows are bubbles and every
retiring row supplies the indexed jump boundary for the next architectural
state.

This is the jump-family counterpart of `RvfiAddiProgram`.  It is deliberately a
program certificate rather than a core model; a loaded-core invariant still
has to establish the indexed `Rv32iBoundary` at each retiring cycle.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## A decoded jump program -/

/-! The semantic JAL/JALR shape retained by one decoded instruction. -/
inductive JumpKind where
  | jal (rd : Reg) (offset : Word)
  | jalr (rd rs1 : Reg) (offset : Word)
  deriving DecidableEq, Repr

namespace JumpKind

def toInstr : JumpKind → Instr
  | .jal rd offset => .jump rd .pc offset
  | .jalr rd rs1 offset => .jump rd (.reg rs1) offset

def next (state : ArchState) : JumpKind → ArchState
  | .jal rd offset => jalNext state rd offset
  | .jalr rd rs1 offset => jalrNext state rd rs1 offset

def retirement (state : ArchState) (input : Input) : JumpKind → Retirement
  | .jal rd offset => jalRetirement state input rd offset
  | .jalr rd rs1 offset => jalrRetirement state input rd rs1 offset

end JumpKind

structure JumpInstruction where
  word : Word
  kind : JumpKind
  decode : Fetched.decode (.word word) = some kind.toInstr

/-- The architectural input associated with one jump instruction. -/
def jumpProgramInput (memory : Memory) (instruction : JumpInstruction) : Input :=
  { fetched := .word instruction.word, memory := memory, irq := 0 }

/-- The cycle/commit inputs for a jump program.  JAL and JALR do not
mutate data memory, so every instruction sees the same threaded memory. -/
def jumpProgramInputs (memory : Memory) : List JumpInstruction → List Input
  | [] => []
  | instruction :: program =>
      jumpProgramInput memory instruction :: jumpProgramInputs memory program

/-- The architectural state after executing a jump program. -/
def jumpProgramState (state : ArchState) : List JumpInstruction → ArchState
  | [] => state
  | instruction :: program =>
      jumpProgramState
        (JumpKind.next state instruction.kind) program

/-- The exact retirement stream for a jump program. -/
def jumpProgramRetirements (memory : Memory) (state : ArchState) :
    List JumpInstruction → List Retirement
  | [] => []
  | instruction :: program =>
      JumpKind.retirement state (jumpProgramInput memory instruction) instruction.kind ::
        jumpProgramRetirements memory
          (JumpKind.next state instruction.kind) program

/-! ## Program-fold composition -/

/-- The input fold preserves list concatenation. -/
theorem jumpProgramInputs_append (memory : Memory)
    (first second : List JumpInstruction) :
    jumpProgramInputs memory (first ++ second) =
      jumpProgramInputs memory first ++ jumpProgramInputs memory second := by
  induction first with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, jumpProgramInputs, ih, List.cons_append]

/-- The architectural jump fold resumes from the state reached by its prefix. -/
theorem jumpProgramState_append (state : ArchState)
    (first second : List JumpInstruction) :
    jumpProgramState state (first ++ second) =
      jumpProgramState (jumpProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, jumpProgramState]
      exact ih (state :=
        JumpKind.next state instruction.kind)

/-- The retirement fold carries the same architectural prefix boundary as the
state fold. -/
theorem jumpProgramRetirements_append (memory : Memory) (state : ArchState)
    (first second : List JumpInstruction) :
    jumpProgramRetirements memory state (first ++ second) =
      jumpProgramRetirements memory state first ++
        jumpProgramRetirements memory (jumpProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, jumpProgramRetirements]
      rw [ih (state :=
        JumpKind.next state instruction.kind)]
      rfl

/-! ## Stateful ISA equations -/

/-- One decoded JAL/JALR instruction drives the exact stateful ISA transition
with no memory update. -/
theorem rvMemoryMachineWith_jump_step
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (instruction : JumpInstruction) :
    (rvMemoryMachineWith profile).step
        { arch := state, memory := memory }
        (jumpProgramInput memory instruction) =
      ({ arch := JumpKind.next state instruction.kind, memory := memory },
        JumpKind.retirement state (jumpProgramInput memory instruction)
          instruction.kind) := by
  cases instruction with
  | mk word kind decode =>
      cases kind with
      | jal rd offset =>
          simp only [rvMemoryMachineWith, jumpProgramInput, JumpKind.toInstr,
            JumpKind.next, JumpKind.retirement] at decode ⊢
          rw [isaStepWith_jal profile state memory word rd offset decode]
          rfl
      | jalr rd rs1 offset =>
          simp only [rvMemoryMachineWith, jumpProgramInput, JumpKind.toInstr,
            JumpKind.next, JumpKind.retirement] at decode ⊢
          rw [isaStepWith_jalr profile state memory word rd rs1 offset decode]
          rfl

/-- Threading the stateful ISA machine through every jump gives the
folded architectural state and unchanged memory. -/
theorem rvMemoryMachineWith_jump_program_state
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (program : List JumpInstruction) :
    machineStateAfter (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (jumpProgramInputs memory program) =
      { arch := jumpProgramState state program, memory := memory } := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [jumpProgramInputs, machineStateAfter]
      rw [rvMemoryMachineWith_jump_step profile state memory instruction]
      simpa [jumpProgramState] using
        (ih (state := JumpKind.next state instruction.kind))

/-- The same jump program has exactly the retirement stream prescribed by its
architectural fold. -/
theorem rvMemoryMachineWith_jump_program_trace
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (program : List JumpInstruction) :
    trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (jumpProgramInputs memory program) =
      jumpProgramRetirements memory state program := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [jumpProgramInputs, trace, jumpProgramRetirements]
      change
        ((rvMemoryMachineWith profile).step
            { arch := state, memory := memory }
            (jumpProgramInput memory instruction)).2 ::
          trace (rvMemoryMachineWith profile)
            ((rvMemoryMachineWith profile).step
              { arch := state, memory := memory }
              (jumpProgramInput memory instruction)).1
            (jumpProgramInputs memory program) = _
      rw [rvMemoryMachineWith_jump_step profile state memory instruction]
      simpa using
        (ih (state := JumpKind.next state instruction.kind))

/-- The stateful jump machine resumes at the exact memory-machine state after
the first program segment. -/
theorem rvMemoryMachineWith_jump_program_state_append
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (first second : List JumpInstruction) :
    machineStateAfter (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (jumpProgramInputs memory (first ++ second)) =
      machineStateAfter (rvMemoryMachineWith profile)
        (machineStateAfter (rvMemoryMachineWith profile)
          { arch := state, memory := memory }
          (jumpProgramInputs memory first))
        (jumpProgramInputs memory second) := by
  rw [jumpProgramInputs_append, machineStateAfter_append]

/-- The stateful jump retirement stream splits at the same first-segment
boundary as the architectural state. -/
theorem rvMemoryMachineWith_jump_program_trace_append
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (first second : List JumpInstruction) :
    trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (jumpProgramInputs memory (first ++ second)) =
      trace (rvMemoryMachineWith profile)
          { arch := state, memory := memory }
          (jumpProgramInputs memory first) ++
        trace (rvMemoryMachineWith profile)
          (machineStateAfter (rvMemoryMachineWith profile)
            { arch := state, memory := memory }
            (jumpProgramInputs memory first))
          (jumpProgramInputs memory second) := by
  rw [jumpProgramInputs_append, machineTrace_append]

/-! ## Raw RVFI certificate for an arbitrary jump program -/

/-- A raw RVFI stream whose retiring rows are exactly the supplied jump
program. -/
inductive JumpRvfiTrace (memory : Memory) :
    Nat → ArchState → List RvfiObservation → List JumpInstruction → Prop where
  | nil (start : Nat) (state : ArchState) :
      JumpRvfiTrace memory start state [] []
  | bubble {start : Nat} {state : ArchState}
      {observation : RvfiObservation} {observations : List RvfiObservation}
      {program : List JumpInstruction}
      (hvalid : observation.valid = false)
      (tail : JumpRvfiTrace memory start state observations program) :
      JumpRvfiTrace memory start state (observation :: observations) program
  | retire {start : Nat} {state : ArchState}
      {observation : RvfiObservation}
      {observations : List RvfiObservation}
      {instruction : JumpInstruction} {program : List JumpInstruction}
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state (jumpProgramInput memory instruction) observation
          { arch := JumpKind.next state instruction.kind,
            memory := memory }
          (JumpKind.retirement state (jumpProgramInput memory instruction) instruction.kind))
      (tail :
        JumpRvfiTrace memory (start + 1)
          (JumpKind.next state instruction.kind)
          observations program) :
      JumpRvfiTrace memory start state (observation :: observations)
        (instruction :: program)

/-- Every symbolic jump certificate is an ordinary RVFI normalization
certificate. -/
theorem JumpRvfiTrace.toRvfiTraceRefines
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List JumpInstruction}
    (certificate : JumpRvfiTrace memory start state observations program) :
    RvfiTraceRefines start observations
      (jumpProgramRetirements memory state program) := by
  induction certificate with
  | nil start state => exact .nil start
  | bubble hvalid tail ih => exact .bubble hvalid ih
  | retire horder boundary tail ih =>
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      exact .retire hspec.1 horder hretirement ih

/-- The executable normalizer accepts exactly the retirement stream specified
by an arbitrary `JumpRvfiTrace` certificate. -/
theorem JumpRvfiTrace.normalize
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List JumpInstruction}
    (certificate : JumpRvfiTrace memory start state observations program) :
    normalizeRvfiTrace? start observations =
      some (jumpProgramRetirements memory state program) :=
  (normalizeRvfiTrace?_iff).2 certificate.toRvfiTraceRefines

/-- The normalized symbolic jump stream is the stateful ISA trace for the same
program. -/
theorem JumpRvfiTrace.trace_refines
    (profile : PlatformProfile)
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List JumpInstruction}
    (certificate : JumpRvfiTrace memory start state observations program) :
    normalizeRvfiTrace? start observations =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (jumpProgramInputs memory program)) := by
  calc
    normalizeRvfiTrace? start observations =
        some (jumpProgramRetirements memory state program) :=
      certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (jumpProgramInputs memory program)) := by
      rw [rvMemoryMachineWith_jump_program_trace]

/-! ## Composing raw jump certificates -/

/-- Raw jump certificates compose at the next retirement order and folded
architectural state produced by the first program chunk. -/
theorem JumpRvfiTrace.append
    {memory : Memory} {start : Nat} {state : ArchState}
    {firstObservations secondObservations : List RvfiObservation}
    {firstProgram secondProgram : List JumpInstruction}
    (first : JumpRvfiTrace memory start state firstObservations firstProgram)
    (second : JumpRvfiTrace memory
      (start + firstProgram.length)
      (jumpProgramState state firstProgram)
      secondObservations secondProgram) :
    JumpRvfiTrace memory start state
      (firstObservations ++ secondObservations)
      (firstProgram ++ secondProgram) := by
  induction first with
  | nil start state =>
      simpa [jumpProgramState] using second
  | bubble hvalid tail ih =>
      refine JumpRvfiTrace.bubble hvalid ?_
      apply ih
      simpa [jumpProgramState] using second
  | retire horder boundary tail ih =>
      refine JumpRvfiTrace.retire horder boundary ?_
      apply ih
      simpa [jumpProgramState, List.length_cons, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using second

/-! ## Input-aware cycle certificate -/

/-- The jump invariant tied to an actual packed-RVFI cycle machine.  Bubble
cycles may carry any input; a retiring cycle must present the exact jump input
whose memory view it reports. -/
inductive JumpRvfiCycleTrace {State : Type}
    (machine : RvfiCycleMachine State) (memory : Memory) :
    Nat → State → ArchState → List Input → List JumpInstruction → Prop where
  | nil (start : Nat) (coreState : State) (state : ArchState) :
      JumpRvfiCycleTrace machine memory start coreState state [] []
  | bubble {start : Nat} {coreState coreState' : State}
      {state : ArchState} {cycleInput : Input} {cycles : List Input}
      {program : List JumpInstruction} {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hvalid : observation.valid = false)
      (tail : JumpRvfiCycleTrace machine memory start coreState' state
        cycles program) :
      JumpRvfiCycleTrace machine memory start coreState state
        (cycleInput :: cycles) program
  | retire {start : Nat} {coreState coreState' : State}
      {state : ArchState} {cycleInput : Input} {cycles : List Input}
      {instruction : JumpInstruction} {program : List JumpInstruction}
      {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hinput : cycleInput = jumpProgramInput memory instruction)
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state (jumpProgramInput memory instruction) observation
          { arch := JumpKind.next state instruction.kind,
            memory := memory }
          (JumpKind.retirement state (jumpProgramInput memory instruction) instruction.kind))
      (tail : JumpRvfiCycleTrace machine memory (start + 1) coreState'
        (JumpKind.next state instruction.kind)
        cycles program) :
      JumpRvfiCycleTrace machine memory start coreState state
        (cycleInput :: cycles) (instruction :: program)

/-- An input-aware jump certificate normalizes the observations emitted by its
actual cycle machine to the symbolic program's retirement stream. -/
theorem JumpRvfiCycleTrace.normalize
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List JumpInstruction}
    (certificate : JumpRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (jumpProgramRetirements memory state program) := by
  induction certificate with
  | nil start coreState state => rfl
  | bubble hstep hvalid tail ih =>
      simp only [rvfiObservations, hstep]
      simp [normalizeRvfiTrace?, hvalid, ih]
  | retire hstep hinput horder boundary tail ih =>
      simp only [rvfiObservations, hstep]
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      simp [normalizeRvfiTrace?, jumpProgramRetirements, hspec.1,
        horder, hretirement, ih]

/-- The cycle inputs retained by an input-aware jump certificate are exactly
the symbolic program inputs; bubbles are removed by the optional adapter. -/
theorem JumpRvfiCycleTrace.retireInputs_eq
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List JumpInstruction}
    (certificate : JumpRvfiCycleTrace machine memory start coreState state
      cycles program) :
    retireInputs machine.toCycleMachine coreState cycles =
      jumpProgramInputs memory program := by
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
            (coreState', some (JumpKind.retirement state (jumpProgramInput memory instruction) instruction.kind)) := by
        simp [RvfiCycleMachine.toCycleMachine, hstep, hretirement]
      simp only [retireInputs, hstep']
      rw [hinput]
      simpa [jumpProgramInputs] using ih

/-- Direct core-stream theorem: an input-aware jump certificate relates the
normalized packed observations to the stateful ISA trace on the machine's own
retiring inputs. -/
theorem JumpRvfiCycleTrace.trace_refines
    {State : Type} (profile : PlatformProfile)
    {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List JumpInstruction}
    (certificate : JumpRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
  calc
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
        some (jumpProgramRetirements memory state program) :=
      certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (jumpProgramInputs memory program)) := by
      rw [rvMemoryMachineWith_jump_program_trace]
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
      rw [certificate.retireInputs_eq]

/-! ## Composing input-aware cycle certificates -/

/-- Input-aware jump certificates compose at the exact state and retirement
order boundary produced by the first program chunk. -/
theorem JumpRvfiCycleTrace.append
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {firstCycles secondCycles : List Input}
    {firstProgram secondProgram : List JumpInstruction}
    (first : JumpRvfiCycleTrace machine memory start coreState state
      firstCycles firstProgram)
    (second : JumpRvfiCycleTrace machine memory
      (start + firstProgram.length)
      (rvfiStateAfter machine coreState firstCycles)
      (jumpProgramState state firstProgram)
      secondCycles secondProgram) :
    JumpRvfiCycleTrace machine memory start coreState state
      (firstCycles ++ secondCycles) (firstProgram ++ secondProgram) := by
  induction first with
  | nil start coreState state =>
      simpa [rvfiStateAfter, jumpProgramState] using second
  | bubble hstep hvalid tail ih =>
      refine JumpRvfiCycleTrace.bubble hstep hvalid ?_
      apply ih
      simpa [rvfiStateAfter, hstep] using second
  | retire hstep hinput horder boundary tail ih =>
      refine JumpRvfiCycleTrace.retire hstep hinput horder boundary ?_
      apply ih
      simpa [rvfiStateAfter, jumpProgramState, hstep, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using second

#print axioms LeanModels.Refine.jumpProgramInputs_append
#print axioms LeanModels.Refine.jumpProgramState_append
#print axioms LeanModels.Refine.jumpProgramRetirements_append
#print axioms LeanModels.Refine.rvMemoryMachineWith_jump_step
#print axioms LeanModels.Refine.rvMemoryMachineWith_jump_program_state
#print axioms LeanModels.Refine.rvMemoryMachineWith_jump_program_trace
#print axioms LeanModels.Refine.rvMemoryMachineWith_jump_program_state_append
#print axioms LeanModels.Refine.rvMemoryMachineWith_jump_program_trace_append
#print axioms LeanModels.Refine.JumpRvfiTrace.toRvfiTraceRefines
#print axioms LeanModels.Refine.JumpRvfiTrace.normalize
#print axioms LeanModels.Refine.JumpRvfiTrace.trace_refines
#print axioms LeanModels.Refine.JumpRvfiTrace.append
#print axioms LeanModels.Refine.JumpRvfiCycleTrace.normalize
#print axioms LeanModels.Refine.JumpRvfiCycleTrace.retireInputs_eq
#print axioms LeanModels.Refine.JumpRvfiCycleTrace.trace_refines
#print axioms LeanModels.Refine.JumpRvfiCycleTrace.append

end LeanModels.Refine
