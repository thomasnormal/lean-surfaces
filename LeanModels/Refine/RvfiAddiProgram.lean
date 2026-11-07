import LeanModels.Refine.RvfiRv32i

/-!
# Symbolic RVFI programs made only of ADDI

The per-cycle ADDI constructor in `RvfiAddi` is the local invariant used by a
loaded core.  This file carries that constructor through an arbitrary program
length.  `AddiRvfiTrace` is a proof-facing certificate over the raw RVFI rows:
invalid rows are bubbles, while every retiring row supplies an indexed
`Rv32iBoundary` whose post-state is the next ADDI state.  Thus a core proof can
instantiate this certificate without introducing a finite captured window or
another instruction dispatcher.

The program-side state and retirement folds are deliberately ordinary lists.
They describe the architectural sequence that the existing stateful ISA
machine must execute; they do not rewrite a core or choose a retirement order.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## A decoded ADDI program -/

/-- One decoded 32-bit ADDI instruction, retaining the original word and its
decoder proof so a core-facing certificate cannot replace it with a guessed
encoding. -/
structure AddiInstruction where
  word : Word
  rd : Reg
  rs1 : Reg
  imm : Word
  decode : Fetched.decode (.word word) =
    some (.alu .add rd (.reg rs1) (.imm imm))

/-- The architectural input associated with one program instruction. -/
def addiProgramInput (memory : Memory) (instruction : AddiInstruction) : Input :=
  { fetched := .word instruction.word, memory := memory, irq := 0 }

/-- The cycle/commit inputs for an ADDI-only program.  ADDI does not mutate
memory, so every instruction sees the same threaded memory value. -/
def addiProgramInputs (memory : Memory) : List AddiInstruction → List Input
  | [] => []
  | instruction :: program =>
      addiProgramInput memory instruction :: addiProgramInputs memory program

/-- The architectural state after executing an ADDI-only program. -/
def addiProgramState (state : ArchState) : List AddiInstruction → ArchState
  | [] => state
  | instruction :: program =>
      addiProgramState
        (addiNext state instruction.rd instruction.rs1 instruction.imm) program

/-- The exact retirement stream for an ADDI-only program, including the
architectural state at each retirement. -/
def addiProgramRetirements (memory : Memory) (state : ArchState) :
    List AddiInstruction → List Retirement
  | [] => []
  | instruction :: program =>
      addiRetirement state (addiProgramInput memory instruction)
          instruction.rd instruction.rs1 instruction.imm ::
        addiProgramRetirements memory
          (addiNext state instruction.rd instruction.rs1 instruction.imm) program

theorem addiProgramState_preserves_WF (state : ArchState)
    (program : List AddiInstruction) (hWF : state.WF) :
    (addiProgramState state program).WF := by
  induction program generalizing state with
  | nil => exact hWF
  | cons instruction program ih =>
      apply ih
      exact addiNext_preserves_WF state instruction.rd instruction.rs1
        instruction.imm hWF

/-- One decoded program instruction drives the exact stateful ISA transition
with no memory update. -/
theorem rvMemoryMachineWith_addi_step
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (instruction : AddiInstruction) :
    (rvMemoryMachineWith profile).step
        { arch := state, memory := memory }
        (addiProgramInput memory instruction) =
      ({ arch := addiNext state instruction.rd instruction.rs1 instruction.imm,
          memory := memory },
        addiRetirement state (addiProgramInput memory instruction)
          instruction.rd instruction.rs1 instruction.imm) := by
  simp only [rvMemoryMachineWith, addiProgramInput]
  rw [isaStepWith_addi profile state memory instruction.word
    instruction.rd instruction.rs1 instruction.imm instruction.decode]
  rfl

/-- Threading the existing stateful ISA machine through every instruction in
the symbolic ADDI program gives the folded architectural state and unchanged
memory. -/
theorem rvMemoryMachineWith_addi_program_state
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (program : List AddiInstruction) :
    machineStateAfter (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (addiProgramInputs memory program) =
      { arch := addiProgramState state program, memory := memory } := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [addiProgramInputs, machineStateAfter]
      rw [rvMemoryMachineWith_addi_step profile state memory instruction]
      simpa [addiProgramState] using
        (ih (state := addiNext state instruction.rd instruction.rs1 instruction.imm))

/-- The same symbolic program has exactly the retirement stream prescribed by
the ADDI architectural contract. -/
theorem rvMemoryMachineWith_addi_program_trace
    (profile : PlatformProfile) (state : ArchState) (memory : Memory)
    (program : List AddiInstruction) :
    trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (addiProgramInputs memory program) =
      addiProgramRetirements memory state program := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [addiProgramInputs, trace, addiProgramRetirements]
      change
        ((rvMemoryMachineWith profile).step
            { arch := state, memory := memory }
            (addiProgramInput memory instruction)).2 ::
          trace (rvMemoryMachineWith profile)
            ((rvMemoryMachineWith profile).step
              { arch := state, memory := memory }
              (addiProgramInput memory instruction)).1
            (addiProgramInputs memory program) = _
      rw [rvMemoryMachineWith_addi_step profile state memory instruction]
      simpa using
        (ih (state := addiNext state instruction.rd instruction.rs1 instruction.imm))

/-! ## Raw RVFI certificate for an arbitrary ADDI program -/

/-- A raw RVFI stream whose retiring rows are exactly the supplied ADDI
program.  The indexed boundary fixes both the architectural post-state and
the semantic retirement; it therefore reuses the unified dispatcher rather
than maintaining a second ADDI-to-ISA interpretation. -/
inductive AddiRvfiTrace (memory : Memory) :
    Nat → ArchState → List RvfiObservation → List AddiInstruction → Prop where
  | nil (start : Nat) (state : ArchState) :
      AddiRvfiTrace memory start state [] []
  | bubble {start : Nat} {state : ArchState}
      {observation : RvfiObservation} {observations : List RvfiObservation}
      {program : List AddiInstruction}
      (hvalid : observation.valid = false)
      (tail : AddiRvfiTrace memory start state observations program) :
      AddiRvfiTrace memory start state (observation :: observations) program
  | retire {start : Nat} {state : ArchState}
      {observation : RvfiObservation}
      {observations : List RvfiObservation}
      {instruction : AddiInstruction} {program : List AddiInstruction}
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state (addiProgramInput memory instruction) observation
          { arch := addiNext state instruction.rd instruction.rs1 instruction.imm,
            memory := memory }
          (addiRetirement state
            (addiProgramInput memory instruction)
            instruction.rd instruction.rs1 instruction.imm))
      (tail :
        AddiRvfiTrace memory (start + 1)
          (addiNext state instruction.rd instruction.rs1 instruction.imm)
          observations program) :
      AddiRvfiTrace memory start state (observation :: observations)
        (instruction :: program)

/-- Every symbolic ADDI certificate is an ordinary RVFI normalization
certificate. -/
theorem AddiRvfiTrace.toRvfiTraceRefines
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List AddiInstruction}
    (certificate : AddiRvfiTrace memory start state observations program) :
    RvfiTraceRefines start observations
      (addiProgramRetirements memory state program) := by
  induction certificate with
  | nil start state => exact .nil start
  | bubble hvalid tail ih => exact .bubble hvalid ih
  | retire horder boundary tail ih =>
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      exact .retire hspec.1 horder hretirement ih

/-- The executable normalizer accepts exactly the retirement stream specified
by an arbitrary `AddiRvfiTrace` certificate. -/
theorem AddiRvfiTrace.normalize
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List AddiInstruction}
    (certificate : AddiRvfiTrace memory start state observations program) :
    normalizeRvfiTrace? start observations =
      some (addiProgramRetirements memory state program) :=
  (normalizeRvfiTrace?_iff).2 certificate.toRvfiTraceRefines

/-- The normalized symbolic RVFI stream is the stateful ISA trace for the same
ADDI program. -/
theorem AddiRvfiTrace.trace_refines
    (profile : PlatformProfile)
    {memory : Memory} {start : Nat} {state : ArchState}
    {observations : List RvfiObservation} {program : List AddiInstruction}
    (certificate : AddiRvfiTrace memory start state observations program)
    : normalizeRvfiTrace? start observations =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (addiProgramInputs memory program)) := by
  calc
    normalizeRvfiTrace? start observations =
        some (addiProgramRetirements memory state program) :=
      certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (addiProgramInputs memory program)) := by
      rw [rvMemoryMachineWith_addi_program_trace]

/-! ## Input-aware cycle certificate -/

/-- The same ADDI invariant tied to an actual packed-RVFI cycle machine.
Bubble cycles may carry any input; a retiring cycle must present the exact
program input whose memory view it reports.  The core state is retained in the
indices, so this certificate can be produced by induction over a loaded
machine's cycle transition without manufacturing an input stream afterward. -/
inductive AddiRvfiCycleTrace {State : Type}
    (machine : RvfiCycleMachine State) (memory : Memory) :
    Nat → State → ArchState → List Input → List AddiInstruction → Prop where
  | nil (start : Nat) (coreState : State) (state : ArchState) :
      AddiRvfiCycleTrace machine memory start coreState state [] []
  | bubble {start : Nat} {coreState coreState' : State}
      {state : ArchState} {cycleInput : Input} {cycles : List Input}
      {program : List AddiInstruction} {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hvalid : observation.valid = false)
      (tail : AddiRvfiCycleTrace machine memory start coreState' state
        cycles program) :
      AddiRvfiCycleTrace machine memory start coreState state
        (cycleInput :: cycles) program
  | retire {start : Nat} {coreState coreState' : State}
      {state : ArchState} {cycleInput : Input} {cycles : List Input}
      {instruction : AddiInstruction} {program : List AddiInstruction}
      {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hinput : cycleInput = addiProgramInput memory instruction)
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state (addiProgramInput memory instruction) observation
          { arch := addiNext state instruction.rd instruction.rs1 instruction.imm,
            memory := memory }
          (addiRetirement state
            (addiProgramInput memory instruction)
            instruction.rd instruction.rs1 instruction.imm))
      (tail : AddiRvfiCycleTrace machine memory (start + 1) coreState'
        (addiNext state instruction.rd instruction.rs1 instruction.imm)
        cycles program) :
      AddiRvfiCycleTrace machine memory start coreState state
        (cycleInput :: cycles) (instruction :: program)

/-- An input-aware ADDI certificate normalizes the observations emitted by its
actual cycle machine to the symbolic program's retirement stream. -/
theorem AddiRvfiCycleTrace.normalize
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List AddiInstruction}
    (certificate : AddiRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (addiProgramRetirements memory state program) := by
  induction certificate with
  | nil start coreState state => rfl
  | bubble hstep hvalid tail ih =>
      simp only [rvfiObservations, hstep]
      simp [normalizeRvfiTrace?, hvalid, ih]
  | retire hstep hinput horder boundary tail ih =>
      simp only [rvfiObservations, hstep]
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      simp [normalizeRvfiTrace?, addiProgramRetirements, hspec.1,
        horder, hretirement, ih]

/-- The cycle inputs retained by an input-aware ADDI certificate are exactly
the symbolic program inputs; bubbles are removed by the existing optional
RVFI adapter. -/
theorem AddiRvfiCycleTrace.retireInputs_eq
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List AddiInstruction}
    (certificate : AddiRvfiCycleTrace machine memory start coreState state
      cycles program) :
    retireInputs machine.toCycleMachine coreState cycles =
      addiProgramInputs memory program := by
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
            (coreState', some (addiRetirement state
              (addiProgramInput memory instruction)
              instruction.rd instruction.rs1 instruction.imm)) := by
        simp [RvfiCycleMachine.toCycleMachine, hstep, hretirement]
      simp only [retireInputs, hstep']
      rw [hinput]
      simpa [addiProgramInputs] using ih

/-- Direct core-stream theorem: an input-aware ADDI certificate relates the
normalized packed observations to the stateful ISA trace on the machine's own
retiring inputs. -/
theorem AddiRvfiCycleTrace.trace_refines
    {State : Type} (profile : PlatformProfile)
    {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List AddiInstruction}
    (certificate : AddiRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
  calc
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
        some (addiProgramRetirements memory state program) :=
      certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (addiProgramInputs memory program)) := by
      rw [rvMemoryMachineWith_addi_program_trace]
    _ = some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
      rw [certificate.retireInputs_eq]

#print axioms LeanModels.Refine.addiProgramState_preserves_WF
#print axioms LeanModels.Refine.rvMemoryMachineWith_addi_program_state
#print axioms LeanModels.Refine.rvMemoryMachineWith_addi_program_trace
#print axioms LeanModels.Refine.AddiRvfiTrace.toRvfiTraceRefines
#print axioms LeanModels.Refine.AddiRvfiTrace.normalize
#print axioms LeanModels.Refine.AddiRvfiTrace.trace_refines
#print axioms LeanModels.Refine.AddiRvfiCycleTrace.normalize
#print axioms LeanModels.Refine.AddiRvfiCycleTrace.retireInputs_eq
#print axioms LeanModels.Refine.AddiRvfiCycleTrace.trace_refines

end LeanModels.Refine
