import LeanModels.Refine.RvfiRv32i
import LeanModels.Refine.Rv32iUpper

/-!
# Symbolic RVFI programs made only of RV32I upper-immediate instructions

`UpperInstruction` retains the fetched word, semantic LUI/AUIPC kind, and decoder proof.
The folds below carry an arbitrary upper-immediate program through the stateful RV32I machine.  `UpperRvfiTrace` is the proof-facing
certificate for a packed RVFI stream: invalid rows are bubbles and every
retiring row supplies the indexed upper boundary for the next architectural
state.

This is the upper-family counterpart of `RvfiAddiProgram`.  It is deliberately a
program certificate rather than a core model; a loaded-core invariant still
has to establish the indexed `Rv32iBoundary` at each retiring cycle.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## A decoded upper program -/

/-! The semantic LUI/AUIPC shape retained by one decoded instruction. -/
inductive UpperKind where
  | lui (rd : Reg) (imm : Word)
  | auipc (rd : Reg) (imm : Word)
  deriving DecidableEq, Repr

namespace UpperKind

def toInstr : UpperKind → Instr
  | .lui rd imm => .alu .add rd (.reg 0) (.imm imm)
  | .auipc rd imm => .alu .add rd .pc (.imm imm)

def next (state : ArchState) : UpperKind → ArchState
  | .lui rd imm => luiNext state rd imm
  | .auipc rd imm => auipcNext state rd imm

def retirement (state : ArchState) (input : Input) : UpperKind → Retirement
  | .lui rd imm => luiRetirement state input rd imm
  | .auipc rd imm => auipcRetirement state input rd imm

end UpperKind

structure UpperInstruction where
  word : Word
  kind : UpperKind
  decode : Fetched.decode (.word word) = some kind.toInstr

/-- The architectural input associated with one upper instruction. -/
def upperProgramInput (memory : Memory) (instruction : UpperInstruction) : Input :=
  { fetched := .word instruction.word, memory := memory, irq := 0 }

/-- The cycle/commit inputs for an upper-immediate program.  LUI and AUIPC do not
mutate data memory, so every instruction sees the same threaded memory. -/
def upperProgramInputs (memory : Memory) : List UpperInstruction → List Input
  | [] => []
  | instruction :: program =>
      upperProgramInput memory instruction :: upperProgramInputs memory program

/-- The architectural state after executing an upper-immediate program. -/
def upperProgramState (state : ArchState) : List UpperInstruction → ArchState
  | [] => state
  | instruction :: program =>
      upperProgramState
        (UpperKind.next state instruction.kind) program

/-- The exact retirement stream for an upper-immediate program. -/
def upperProgramRetirements (memory : Memory) (state : ArchState) :
    List UpperInstruction → List Retirement
  | [] => []
  | instruction :: program =>
      UpperKind.retirement state (upperProgramInput memory instruction) instruction.kind ::
        upperProgramRetirements memory
          (UpperKind.next state instruction.kind) program

/-! ## Program-fold composition -/

/-- The input fold preserves list concatenation. -/
theorem upperProgramInputs_append (memory : Memory)
    (first second : List UpperInstruction) :
    upperProgramInputs memory (first ++ second) =
      upperProgramInputs memory first ++ upperProgramInputs memory second := by
  induction first with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, upperProgramInputs, ih, List.cons_append]

/-- The architectural upper fold resumes from the state reached by its prefix. -/
theorem upperProgramState_append (state : ArchState)
    (first second : List UpperInstruction) :
    upperProgramState state (first ++ second) =
      upperProgramState (upperProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, upperProgramState]
      exact ih (state :=
        UpperKind.next state instruction.kind)

/-- The retirement fold carries the same architectural prefix boundary as the
state fold. -/
theorem upperProgramRetirements_append (memory : Memory) (state : ArchState)
    (first second : List UpperInstruction) :
    upperProgramRetirements memory state (first ++ second) =
      upperProgramRetirements memory state first ++
        upperProgramRetirements memory (upperProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, upperProgramRetirements]
      rw [ih (state :=
        UpperKind.next state instruction.kind)]
      rfl

/-! ## Stateful ISA equations -/

/-- One decoded LUI/AUIPC instruction drives the exact stateful ISA transition
with no memory update. -/
theorem rvMemoryMachineWith_upper_step
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (instruction : UpperInstruction) :
    (rvMemoryMachineWith profile).step
        { arch := state, memory := memory }
        (upperProgramInput memory instruction) =
      ({ arch := UpperKind.next state instruction.kind, memory := memory },
        UpperKind.retirement state (upperProgramInput memory instruction)
          instruction.kind) := by
  cases instruction with
  | mk word kind decode =>
      cases kind with
      | lui rd imm =>
          simp only [rvMemoryMachineWith, upperProgramInput, UpperKind.toInstr,
            UpperKind.next, UpperKind.retirement] at decode ⊢
          rw [isaStepWith_lui profile state memory word rd imm decode]
          rfl
      | auipc rd imm =>
          simp only [rvMemoryMachineWith, upperProgramInput, UpperKind.toInstr,
            UpperKind.next, UpperKind.retirement] at decode ⊢
          rw [isaStepWith_auipc profile state memory word rd imm decode]
          rfl

/-- Threading the stateful ISA machine through every upper-immediate instruction gives the
folded architectural state and unchanged memory. -/
theorem rvMemoryMachineWith_upper_program_state
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (program : List UpperInstruction) :
    machineStateAfter (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (upperProgramInputs memory program) =
      { arch := upperProgramState state program, memory := memory } := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [upperProgramInputs, machineStateAfter]
      rw [rvMemoryMachineWith_upper_step profile state memory instruction]
      simpa [upperProgramState] using
        (ih (state := UpperKind.next state instruction.kind))

/-- The same upper program has exactly the retirement stream prescribed by its
architectural fold. -/
theorem rvMemoryMachineWith_upper_program_trace
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (program : List UpperInstruction) :
    trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (upperProgramInputs memory program) =
      upperProgramRetirements memory state program := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [upperProgramInputs, trace, upperProgramRetirements]
      change
        ((rvMemoryMachineWith profile).step
            { arch := state, memory := memory }
            (upperProgramInput memory instruction)).2 ::
          trace (rvMemoryMachineWith profile)
            ((rvMemoryMachineWith profile).step
              { arch := state, memory := memory }
              (upperProgramInput memory instruction)).1
            (upperProgramInputs memory program) = _
      rw [rvMemoryMachineWith_upper_step profile state memory instruction]
      simpa using
        (ih (state := UpperKind.next state instruction.kind))

/-- The stateful upper machine resumes at the exact memory-machine state after
the first program segment. -/
theorem rvMemoryMachineWith_upper_program_state_append
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (first second : List UpperInstruction) :
    machineStateAfter (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (upperProgramInputs memory (first ++ second)) =
      machineStateAfter (rvMemoryMachineWith profile)
        (machineStateAfter (rvMemoryMachineWith profile)
          { arch := state, memory := memory }
          (upperProgramInputs memory first))
        (upperProgramInputs memory second) := by
  rw [upperProgramInputs_append, machineStateAfter_append]

/-- The stateful upper retirement stream splits at the same first-segment
boundary as the architectural state. -/
theorem rvMemoryMachineWith_upper_program_trace_append
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (first second : List UpperInstruction) :
    trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (upperProgramInputs memory (first ++ second)) =
      trace (rvMemoryMachineWith profile)
          { arch := state, memory := memory }
          (upperProgramInputs memory first) ++
        trace (rvMemoryMachineWith profile)
          (machineStateAfter (rvMemoryMachineWith profile)
            { arch := state, memory := memory }
            (upperProgramInputs memory first))
          (upperProgramInputs memory second) := by
  rw [upperProgramInputs_append, machineTrace_append]

/-! ## Raw RVFI certificate for an arbitrary upper program -/

/-- A raw RVFI stream whose retiring rows are exactly the supplied upper
program. -/
inductive UpperRvfiTrace (memory : Memory) :
    Nat → ArchState → List RvfiObservation → List UpperInstruction → Prop where
  | nil (start : Nat) (state : ArchState) :
      UpperRvfiTrace memory start state [] []
  | bubble {start : Nat} {state : ArchState}
      {observation : RvfiObservation} {observations : List RvfiObservation}
      {program : List UpperInstruction}
      (hvalid : observation.valid = false)
      (tail : UpperRvfiTrace memory start state observations program) :
      UpperRvfiTrace memory start state (observation :: observations) program
  | retire {start : Nat} {state : ArchState}
      {observation : RvfiObservation}
      {observations : List RvfiObservation}
      {instruction : UpperInstruction} {program : List UpperInstruction}
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state (upperProgramInput memory instruction) observation
          { arch := UpperKind.next state instruction.kind,
            memory := memory }
          (UpperKind.retirement state (upperProgramInput memory instruction) instruction.kind))
      (tail :
        UpperRvfiTrace memory (start + 1)
          (UpperKind.next state instruction.kind)
          observations program) :
      UpperRvfiTrace memory start state (observation :: observations)
        (instruction :: program)

/-- Every symbolic upper-immediate certificate is an ordinary RVFI normalization
certificate. -/
theorem UpperRvfiTrace.toRvfiTraceRefines
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List UpperInstruction}
    (certificate : UpperRvfiTrace memory start state observations program) :
    RvfiTraceRefines start observations
      (upperProgramRetirements memory state program) := by
  induction certificate with
  | nil start state => exact .nil start
  | bubble hvalid tail ih => exact .bubble hvalid ih
  | retire horder boundary tail ih =>
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      exact .retire hspec.1 horder hretirement ih

/-- The executable normalizer accepts exactly the retirement stream specified
by an arbitrary `UpperRvfiTrace` certificate. -/
theorem UpperRvfiTrace.normalize
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List UpperInstruction}
    (certificate : UpperRvfiTrace memory start state observations program) :
    normalizeRvfiTrace? start observations =
      some (upperProgramRetirements memory state program) :=
  (normalizeRvfiTrace?_iff).2 certificate.toRvfiTraceRefines

/-- The normalized symbolic upper-immediate stream is the stateful ISA trace for the same
program. -/
theorem UpperRvfiTrace.trace_refines
    (profile : PlatformProfile)
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List UpperInstruction}
    (certificate : UpperRvfiTrace memory start state observations program) :
    normalizeRvfiTrace? start observations =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (upperProgramInputs memory program)) := by
  calc
    normalizeRvfiTrace? start observations =
        some (upperProgramRetirements memory state program) :=
      certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (upperProgramInputs memory program)) := by
      rw [rvMemoryMachineWith_upper_program_trace]

/-! ## Composing raw upper-immediate certificates -/

/-- Raw upper-immediate certificates compose at the next retirement order and folded
architectural state produced by the first program chunk. -/
theorem UpperRvfiTrace.append
    {memory : Memory} {start : Nat} {state : ArchState}
    {firstObservations secondObservations : List RvfiObservation}
    {firstProgram secondProgram : List UpperInstruction}
    (first : UpperRvfiTrace memory start state firstObservations firstProgram)
    (second : UpperRvfiTrace memory
      (start + firstProgram.length)
      (upperProgramState state firstProgram)
      secondObservations secondProgram) :
    UpperRvfiTrace memory start state
      (firstObservations ++ secondObservations)
      (firstProgram ++ secondProgram) := by
  induction first with
  | nil start state =>
      simpa [upperProgramState] using second
  | bubble hvalid tail ih =>
      refine UpperRvfiTrace.bubble hvalid ?_
      apply ih
      simpa [upperProgramState] using second
  | retire horder boundary tail ih =>
      refine UpperRvfiTrace.retire horder boundary ?_
      apply ih
      simpa [upperProgramState, List.length_cons, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using second

/-! ## Input-aware cycle certificate -/

/-- The upper invariant tied to an actual packed-RVFI cycle machine.  Bubble
cycles may carry any input; a retiring cycle must present the exact upper-immediate input
whose memory view it reports. -/
inductive UpperRvfiCycleTrace {State : Type}
    (machine : RvfiCycleMachine State) (memory : Memory) :
    Nat → State → ArchState → List Input → List UpperInstruction → Prop where
  | nil (start : Nat) (coreState : State) (state : ArchState) :
      UpperRvfiCycleTrace machine memory start coreState state [] []
  | bubble {start : Nat} {coreState coreState' : State}
      {state : ArchState} {cycleInput : Input} {cycles : List Input}
      {program : List UpperInstruction} {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hvalid : observation.valid = false)
      (tail : UpperRvfiCycleTrace machine memory start coreState' state
        cycles program) :
      UpperRvfiCycleTrace machine memory start coreState state
        (cycleInput :: cycles) program
  | retire {start : Nat} {coreState coreState' : State}
      {state : ArchState} {cycleInput : Input} {cycles : List Input}
      {instruction : UpperInstruction} {program : List UpperInstruction}
      {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hinput : cycleInput = upperProgramInput memory instruction)
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state (upperProgramInput memory instruction) observation
          { arch := UpperKind.next state instruction.kind,
            memory := memory }
          (UpperKind.retirement state (upperProgramInput memory instruction) instruction.kind))
      (tail : UpperRvfiCycleTrace machine memory (start + 1) coreState'
        (UpperKind.next state instruction.kind)
        cycles program) :
      UpperRvfiCycleTrace machine memory start coreState state
        (cycleInput :: cycles) (instruction :: program)

/-- An input-aware upper-immediate certificate normalizes the observations emitted by its
actual cycle machine to the symbolic program's retirement stream. -/
theorem UpperRvfiCycleTrace.normalize
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List UpperInstruction}
    (certificate : UpperRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (upperProgramRetirements memory state program) := by
  induction certificate with
  | nil start coreState state => rfl
  | bubble hstep hvalid tail ih =>
      simp only [rvfiObservations, hstep]
      simp [normalizeRvfiTrace?, hvalid, ih]
  | retire hstep hinput horder boundary tail ih =>
      simp only [rvfiObservations, hstep]
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      simp [normalizeRvfiTrace?, upperProgramRetirements, hspec.1,
        horder, hretirement, ih]

/-- The cycle inputs retained by an input-aware upper-immediate certificate are exactly
the symbolic program inputs; bubbles are removed by the optional adapter. -/
theorem UpperRvfiCycleTrace.retireInputs_eq
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List UpperInstruction}
    (certificate : UpperRvfiCycleTrace machine memory start coreState state
      cycles program) :
    retireInputs machine.toCycleMachine coreState cycles =
      upperProgramInputs memory program := by
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
            (coreState', some (UpperKind.retirement state (upperProgramInput memory instruction) instruction.kind)) := by
        simp [RvfiCycleMachine.toCycleMachine, hstep, hretirement]
      simp only [retireInputs, hstep']
      rw [hinput]
      simpa [upperProgramInputs] using ih

/-- Direct core-stream theorem: an input-aware upper-immediate certificate relates the
normalized packed observations to the stateful ISA trace on the machine's own
retiring inputs. -/
theorem UpperRvfiCycleTrace.trace_refines
    {State : Type} (profile : PlatformProfile)
    {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List UpperInstruction}
    (certificate : UpperRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
  calc
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
        some (upperProgramRetirements memory state program) :=
      certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (upperProgramInputs memory program)) := by
      rw [rvMemoryMachineWith_upper_program_trace]
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
      rw [certificate.retireInputs_eq]

/-! ## Composing input-aware cycle certificates -/

/-- Input-aware upper-immediate certificates compose at the exact state and retirement
order boundary produced by the first program chunk. -/
theorem UpperRvfiCycleTrace.append
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {firstCycles secondCycles : List Input}
    {firstProgram secondProgram : List UpperInstruction}
    (first : UpperRvfiCycleTrace machine memory start coreState state
      firstCycles firstProgram)
    (second : UpperRvfiCycleTrace machine memory
      (start + firstProgram.length)
      (rvfiStateAfter machine coreState firstCycles)
      (upperProgramState state firstProgram)
      secondCycles secondProgram) :
    UpperRvfiCycleTrace machine memory start coreState state
      (firstCycles ++ secondCycles) (firstProgram ++ secondProgram) := by
  induction first with
  | nil start coreState state =>
      simpa [rvfiStateAfter, upperProgramState] using second
  | bubble hstep hvalid tail ih =>
      refine UpperRvfiCycleTrace.bubble hstep hvalid ?_
      apply ih
      simpa [rvfiStateAfter, hstep] using second
  | retire hstep hinput horder boundary tail ih =>
      refine UpperRvfiCycleTrace.retire hstep hinput horder boundary ?_
      apply ih
      simpa [rvfiStateAfter, upperProgramState, hstep, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using second

#print axioms LeanModels.Refine.upperProgramInputs_append
#print axioms LeanModels.Refine.upperProgramState_append
#print axioms LeanModels.Refine.upperProgramRetirements_append
#print axioms LeanModels.Refine.rvMemoryMachineWith_upper_step
#print axioms LeanModels.Refine.rvMemoryMachineWith_upper_program_state
#print axioms LeanModels.Refine.rvMemoryMachineWith_upper_program_trace
#print axioms LeanModels.Refine.rvMemoryMachineWith_upper_program_state_append
#print axioms LeanModels.Refine.rvMemoryMachineWith_upper_program_trace_append
#print axioms LeanModels.Refine.UpperRvfiTrace.toRvfiTraceRefines
#print axioms LeanModels.Refine.UpperRvfiTrace.normalize
#print axioms LeanModels.Refine.UpperRvfiTrace.trace_refines
#print axioms LeanModels.Refine.UpperRvfiTrace.append
#print axioms LeanModels.Refine.UpperRvfiCycleTrace.normalize
#print axioms LeanModels.Refine.UpperRvfiCycleTrace.retireInputs_eq
#print axioms LeanModels.Refine.UpperRvfiCycleTrace.trace_refines
#print axioms LeanModels.Refine.UpperRvfiCycleTrace.append

end LeanModels.Refine
