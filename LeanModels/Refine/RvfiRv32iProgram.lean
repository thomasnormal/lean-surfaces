import LeanModels.Refine.RvfiRv32i
import LeanModels.Refine.RvfiAluProgram
import LeanModels.Refine.RvfiBranchProgram
import LeanModels.Refine.RvfiJumpProgram
import LeanModels.Refine.RvfiMemProgram
import LeanModels.Refine.RvfiFenceProgram
import LeanModels.Refine.RvfiSystemProgram
import LeanModels.Refine.RvfiCsrProgram
import LeanModels.Refine.RvfiTrapProgram

/-!
# Symbolic mixed RV32I programs

The family certificates each cover one instruction class.  A loaded core's
retirement stream is mixed, however, so its invariant needs one indexed
program surface that keeps the family choice and every parser-derived proof.
`Rv32iInstruction` is that union.  Its state, input, and retirement folds
thread byte memory through arbitrary mixed lists without introducing a second
instruction decoder.

`Rv32iRvfiTrace` and `Rv32iRvfiCycleTrace` are the corresponding proof-facing
certificates.  A valid row must supply the unified `Rv32iBoundary` at the exact
post-state and retirement selected by the instruction; invalid rows remain
explicit bubbles.  The cycle certificate retains the core's actual inputs and
state at every cycle, so a future loaded-core proof can instantiate it directly.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## The mixed instruction union and folds -/

/-- One decoded instruction from the admitted RV32I boundary. -/
inductive Rv32iInstruction where
  | alu (instruction : AluInstruction)
  | branch (instruction : BranchInstruction)
  | jump (instruction : JumpInstruction)
  | memory (instruction : MemInstruction)
  | fence (instruction : FenceInstruction)
  | system (instruction : SystemInstruction)
  | csr (instruction : CsrInstruction)
  | trap (instruction : TrapInstruction)

namespace Rv32iInstruction

/-! The mixed union keeps one source word and one parser-derived decode proof
for every admitted instruction.  These accessors expose that common fact to a
loaded-core invariant without introducing another decoder. -/

/-- The source word retained by a mixed instruction. -/
def wordOf : Rv32iInstruction → Word
  | .alu instruction => instruction.word
  | .branch instruction => instruction.word
  | .jump instruction => instruction.word
  | .memory instruction => instruction.word
  | .fence instruction => instruction.word
  | .system instruction => instruction.word
  | .csr instruction => instruction.word
  | .trap instruction => instruction.wordOf

/-- The single semantic instruction described by the retained decode proof. -/
def decoded : Rv32iInstruction → Option Instr
  | .alu instruction => some (.alu instruction.op instruction.rd
      instruction.src1 instruction.src2)
  | .branch instruction => some (.branch instruction.cond instruction.rs1
      instruction.rs2 instruction.offset)
  | .jump instruction => some instruction.kind.toInstr
  | .memory instruction => some
      (instruction.kind.toInstr instruction.r instruction.rs1 instruction.imm)
  | .fence instruction => some (.system instruction.kind.toSysOp)
  | .system instruction => some (.system instruction.kind.toSysOp)
  | .csr instruction => some instruction.kind.toInstr
  | .trap instruction =>
      match instruction with
      | .word _ _ => none
      | .csr _ kind _ _ => some kind.toInstr

/-- The parser decoder agrees with the mixed instruction's retained evidence. -/
theorem decode_word (instruction : Rv32iInstruction) :
    Fetched.decode (.word instruction.wordOf) = instruction.decoded := by
  cases instruction with
  | alu instruction => exact instruction.decode
  | branch instruction => exact instruction.decode
  | jump instruction => exact instruction.decode
  | memory instruction => exact instruction.decode
  | fence instruction => exact instruction.decode
  | system instruction => exact instruction.decode
  | csr instruction => exact instruction.decode
  | trap instruction =>
      cases instruction with
      | word word decode => exact decode
      | csr word kind decode row => exact decode

end Rv32iInstruction

/-- The input presented to one mixed instruction at its threaded state. -/
def rv32iProgramInput (state : RvMemoryState) : Rv32iInstruction → Input
  | .alu instruction => aluProgramInput state.memory instruction
  | .branch instruction => branchProgramInput state.memory instruction
  | .jump instruction => jumpProgramInput state.memory instruction
  | .memory instruction => memProgramInput state instruction
  | .fence instruction => fenceProgramInput state.memory instruction
  | .system instruction => systemProgramInput state.memory instruction
  | .csr instruction => csrProgramInput state.memory instruction
  | .trap instruction => trapProgramInput state.memory instruction

/-- The cycle input for a mixed instruction carries its retained source word. -/
theorem rv32iProgramInput_fetched (state : RvMemoryState)
    (instruction : Rv32iInstruction) :
    (rv32iProgramInput state instruction).fetched =
      .word instruction.wordOf := by
  cases instruction with
  | alu instruction => rfl
  | branch instruction => rfl
  | jump instruction => rfl
  | memory instruction => rfl
  | fence instruction => rfl
  | system instruction => rfl
  | csr instruction => rfl
  | trap instruction =>
      cases instruction <;> rfl

/-- The stateful architectural and byte-memory transition for one instruction. -/
def rv32iProgramStep (state : RvMemoryState) : Rv32iInstruction → RvMemoryState
  | .alu instruction =>
      { arch := aluNext state.arch instruction.op instruction.rd instruction.src1
          instruction.src2, memory := state.memory }
  | .branch instruction =>
      { arch := branchNext state.arch instruction.cond instruction.rs1
          instruction.rs2 instruction.offset, memory := state.memory }
  | .jump instruction =>
      { arch := JumpKind.next state.arch instruction.kind, memory := state.memory }
  | .memory instruction => memProgramStep state instruction
  | .fence instruction =>
      { arch := fenceNext state.arch instruction.kind, memory := state.memory }
  | .system instruction =>
      { arch := systemNext state.arch instruction.kind, memory := state.memory }
  | .csr instruction =>
      { arch := csrNext state.arch instruction.row instruction.kind,
        memory := state.memory }
  | .trap _ =>
      { arch := illegalNext state.arch, memory := state.memory }

/-- The retirement emitted by one mixed instruction. -/
def rv32iProgramRetirement (state : RvMemoryState)
    (instruction : Rv32iInstruction) : Retirement :=
  match instruction with
  | .alu instruction =>
      aluRetirement state.arch (aluProgramInput state.memory instruction)
        instruction.op instruction.rd instruction.src1 instruction.src2
  | .branch instruction =>
      branchRetirement state.arch (branchProgramInput state.memory instruction)
        instruction.cond instruction.rs1 instruction.rs2 instruction.offset
  | .jump instruction =>
      JumpKind.retirement state.arch (jumpProgramInput state.memory instruction)
        instruction.kind
  | .memory instruction =>
      memRetirement state.arch (memProgramInput state instruction)
        instruction.kind instruction.r instruction.rs1 instruction.imm
  | .fence instruction =>
      fenceRetirement state.arch (fenceProgramInput state.memory instruction)
        instruction.kind
  | .system instruction =>
      systemRetirement state.arch (systemProgramInput state.memory instruction)
        instruction.kind
  | .csr instruction =>
      csrRetirement state.arch (csrProgramInput state.memory instruction)
        instruction.row instruction.kind
  | .trap instruction =>
      illegalRetirement state.arch (trapProgramInput state.memory instruction)

/-- The cycle inputs for a mixed program, with memory from the preceding state. -/
def rv32iProgramInputs : RvMemoryState → List Rv32iInstruction → List Input
  | _, [] => []
  | state, instruction :: program =>
      rv32iProgramInput state instruction ::
        rv32iProgramInputs (rv32iProgramStep state instruction) program

/-- The threaded state after a mixed program. -/
def rv32iProgramState : RvMemoryState → List Rv32iInstruction → RvMemoryState
  | state, [] => state
  | state, instruction :: program =>
      rv32iProgramState (rv32iProgramStep state instruction) program

/-- The exact retirement stream for a mixed program. -/
def rv32iProgramRetirements : RvMemoryState → List Rv32iInstruction →
    List Retirement
  | _, [] => []
  | state, instruction :: program =>
      rv32iProgramRetirement state instruction ::
        rv32iProgramRetirements (rv32iProgramStep state instruction) program

/-! ## Program-fold laws -/

theorem rv32iProgramInputs_append (state : RvMemoryState)
    (first second : List Rv32iInstruction) :
    rv32iProgramInputs state (first ++ second) =
      rv32iProgramInputs state first ++
        rv32iProgramInputs (rv32iProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, rv32iProgramInputs, rv32iProgramState]
      simp [ih (state := rv32iProgramStep state instruction)]

theorem rv32iProgramState_append (state : RvMemoryState)
    (first second : List Rv32iInstruction) :
    rv32iProgramState state (first ++ second) =
      rv32iProgramState (rv32iProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, rv32iProgramState]
      exact ih (state := rv32iProgramStep state instruction)

theorem rv32iProgramRetirements_append (state : RvMemoryState)
    (first second : List Rv32iInstruction) :
    rv32iProgramRetirements state (first ++ second) =
      rv32iProgramRetirements state first ++
        rv32iProgramRetirements (rv32iProgramState state first) second := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction first ih =>
      simp only [List.cons_append, rv32iProgramRetirements]
      rw [ih (state := rv32iProgramStep state instruction)]
      rfl

/-! ## Stateful ISA equations -/

/-- Every mixed instruction dispatches to its existing family theorem. -/
theorem rvMemoryMachineWith_rv32i_step
    (profile : PlatformProfile) (state : RvMemoryState)
    (instruction : Rv32iInstruction) :
    (rvMemoryMachineWith profile).step state
        (rv32iProgramInput state instruction) =
      (rv32iProgramStep state instruction,
        rv32iProgramRetirement state instruction) := by
  cases instruction with
  | alu instruction =>
      simpa [rv32iProgramInput, rv32iProgramStep, rv32iProgramRetirement] using
        (rvMemoryMachineWith_alu_step profile state.arch state.memory instruction)
  | branch instruction =>
      simpa [rv32iProgramInput, rv32iProgramStep, rv32iProgramRetirement] using
        (rvMemoryMachineWith_branch_step profile state.arch state.memory instruction)
  | jump instruction =>
      simpa [rv32iProgramInput, rv32iProgramStep, rv32iProgramRetirement] using
        (rvMemoryMachineWith_jump_step profile state.arch state.memory instruction)
  | memory instruction =>
      simpa [rv32iProgramInput, rv32iProgramStep, rv32iProgramRetirement] using
        (rvMemoryMachineWith_mem_step profile state instruction)
  | fence instruction =>
      simpa [rv32iProgramInput, rv32iProgramStep, rv32iProgramRetirement] using
        (rvMemoryMachineWith_fence_step profile state.arch state.memory instruction)
  | system instruction =>
      simpa [rv32iProgramInput, rv32iProgramStep, rv32iProgramRetirement] using
        (rvMemoryMachineWith_system_step profile state.arch state.memory instruction)
  | csr instruction =>
      simpa [rv32iProgramInput, rv32iProgramStep, rv32iProgramRetirement] using
        (rvMemoryMachineWith_csr_step profile state.arch state.memory instruction)
  | trap instruction =>
      simpa [rv32iProgramInput, rv32iProgramStep, rv32iProgramRetirement] using
        (rvMemoryMachineWith_trap_step profile state.arch state.memory instruction)

theorem rvMemoryMachineWith_rv32i_program_state
    (profile : PlatformProfile) (state : RvMemoryState)
    (program : List Rv32iInstruction) :
    machineStateAfter (rvMemoryMachineWith profile) state
        (rv32iProgramInputs state program) =
      rv32iProgramState state program := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [rv32iProgramInputs, machineStateAfter]
      rw [rvMemoryMachineWith_rv32i_step profile state instruction]
      simpa [rv32iProgramState] using
        (ih (state := rv32iProgramStep state instruction))

/-- The mixed program state is the stateful machine's public
`rvMemoryStateAfter` result, in the exact form consumed by the R2 headline. -/
theorem rvMemoryStateAfter_rv32i_program
    (profile : PlatformProfile) (state : RvMemoryState)
    (program : List Rv32iInstruction) :
    rvMemoryStateAfter profile state (rv32iProgramInputs state program) =
      rv32iProgramState state program := by
  exact rvMemoryMachineWith_rv32i_program_state profile state program

theorem rvMemoryMachineWith_rv32i_program_trace
    (profile : PlatformProfile) (state : RvMemoryState)
    (program : List Rv32iInstruction) :
    trace (rvMemoryMachineWith profile) state
        (rv32iProgramInputs state program) =
      rv32iProgramRetirements state program := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction program ih =>
      simp only [rv32iProgramInputs, trace, rv32iProgramRetirements]
      change
        ((rvMemoryMachineWith profile).step state
            (rv32iProgramInput state instruction)).2 ::
          trace (rvMemoryMachineWith profile)
            ((rvMemoryMachineWith profile).step state
              (rv32iProgramInput state instruction)).1
            (rv32iProgramInputs (rv32iProgramStep state instruction) program) = _
      rw [rvMemoryMachineWith_rv32i_step profile state instruction]
      simpa using
        (ih (state := rv32iProgramStep state instruction))

theorem rvMemoryMachineWith_rv32i_program_state_append
    (profile : PlatformProfile) (state : RvMemoryState)
    (first second : List Rv32iInstruction) :
    machineStateAfter (rvMemoryMachineWith profile) state
        (rv32iProgramInputs state (first ++ second)) =
      machineStateAfter (rvMemoryMachineWith profile)
        (machineStateAfter (rvMemoryMachineWith profile) state
          (rv32iProgramInputs state first))
        (rv32iProgramInputs (rv32iProgramState state first) second) := by
  rw [rv32iProgramInputs_append, machineStateAfter_append]

theorem rvMemoryMachineWith_rv32i_program_trace_append
    (profile : PlatformProfile) (state : RvMemoryState)
    (first second : List Rv32iInstruction) :
    trace (rvMemoryMachineWith profile) state
        (rv32iProgramInputs state (first ++ second)) =
      trace (rvMemoryMachineWith profile) state
          (rv32iProgramInputs state first) ++
        trace (rvMemoryMachineWith profile)
          (machineStateAfter (rvMemoryMachineWith profile) state
            (rv32iProgramInputs state first))
          (rv32iProgramInputs (rv32iProgramState state first) second) := by
  rw [rv32iProgramInputs_append, machineTrace_append]

/-! ## Core-facing mixed dispatcher -/

/-- A loaded core can discharge the strict cycle contract by identifying the
family instruction represented by each valid row.  The input equality keeps
the exact fetched word, irq bit, and threaded memory at the invariant boundary;
the indexed mixed boundary then supplies the ISA post-state and retirement.
Invalid rows remain explicit ISA stutters through the generic dispatcher. -/
theorem rvfiCycleStepRefines_of_rv32i_program
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hinit : rel machine.init (rvMemoryMachineWith profile).init)
    (hstep : ∀ (state : State) (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ instruction,
          input = rv32iProgramInput memoryState instruction ∧
          Rv32iBoundary memoryState.arch input observation
            (rv32iProgramStep memoryState instruction)
            (rv32iProgramRetirement memoryState instruction) ∧
          rel state' (rv32iProgramStep memoryState instruction)
      else rel state' memoryState) :
    RvfiCycleStepRefines machine (rvMemoryMachineWith profile) rel admit := by
  refine rvfiCycleStepRefines_of_rv32i_memory profile machine rel admit hinit ?_
  intro state memoryState input hrel hadmit
  have hcase := hstep state memoryState input hrel hadmit
  rcases hmachine : machine.step state input with ⟨state', observation⟩
  simp only [hmachine] at hcase ⊢
  by_cases hv : observation.valid = true
  · have hcase' : ∃ instruction,
        input = rv32iProgramInput memoryState instruction ∧
        Rv32iBoundary memoryState.arch input observation
          (rv32iProgramStep memoryState instruction)
          (rv32iProgramRetirement memoryState instruction) ∧
        rel state' (rv32iProgramStep memoryState instruction) := by
      simpa [hv] using hcase
    rcases hcase' with ⟨instruction, hinput, hboundary, hrel'⟩
    simp only [hv]
    refine ⟨rv32iProgramStep memoryState instruction,
      rv32iProgramRetirement memoryState instruction, ?_, hboundary, hrel'⟩
    rw [hinput]
    cases instruction <;> rfl
  · have hv' : observation.valid = false := by
      cases hvalue : observation.valid with
      | false => exact rfl
      | true => exact False.elim (hv hvalue)
    have hrel' : rel state' memoryState := by
      simpa [hv, hv'] using hcase
    simp only [hv]
    exact hrel'

/-! ## Constructing a mixed cycle certificate from a core invariant -/

/- A loaded-core proof usually establishes the indexed family witness while
   stepping the actual core.  The order tag is a separate wire invariant, so
   keep it explicit here rather than hiding it in the optional retirement
   adapter. -/

/-- The per-cycle obligation needed to expose a mixed RV32I certificate.

The witness retains the exact cycle order, input, indexed post-state, and
retirement.  Invalid rows carry the core relation across an ISA stutter. -/
def Rv32iCycleStepRefines {State : Type}
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop) : Prop :=
  ∀ (start : Nat) (state : State) (memoryState : RvMemoryState)
    (input : Input),
    rel state memoryState → admit input →
    let (state', observation) := machine.step state input
    if observation.valid then
      ∃ instruction,
        input = rv32iProgramInput memoryState instruction ∧
        observation.order = start ∧
        Rv32iBoundary memoryState.arch input observation
          (rv32iProgramStep memoryState instruction)
          (rv32iProgramRetirement memoryState instruction) ∧
        rel state' (rv32iProgramStep memoryState instruction)
    else rel state' memoryState

/-! ## Raw RVFI certificate -/

/-- A raw RVFI stream for an arbitrary mixed RV32I program. -/
inductive Rv32iRvfiTrace (memory : Memory) :
    Nat → RvMemoryState → List RvfiObservation → List Rv32iInstruction → Prop where
  | nil (start : Nat) (state : RvMemoryState) :
      Rv32iRvfiTrace memory start state [] []
  | bubble {start : Nat} {state : RvMemoryState}
      {observation : RvfiObservation} {observations : List RvfiObservation}
      {program : List Rv32iInstruction}
      (hvalid : observation.valid = false)
      (tail : Rv32iRvfiTrace memory start state observations program) :
      Rv32iRvfiTrace memory start state (observation :: observations) program
  | retire {start : Nat} {state : RvMemoryState}
      {observation : RvfiObservation} {observations : List RvfiObservation}
      {instruction : Rv32iInstruction} {program : List Rv32iInstruction}
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state.arch (rv32iProgramInput state instruction) observation
          (rv32iProgramStep state instruction) (rv32iProgramRetirement state instruction))
      (tail : Rv32iRvfiTrace memory (start + 1)
        (rv32iProgramStep state instruction) observations program) :
      Rv32iRvfiTrace memory start state (observation :: observations)
        (instruction :: program)

theorem Rv32iRvfiTrace.toRvfiTraceRefines
    {memory : Memory} {start : Nat} {state : RvMemoryState}
    {observations : List RvfiObservation} {program : List Rv32iInstruction}
    (certificate : Rv32iRvfiTrace memory start state observations program) :
    RvfiTraceRefines start observations
      (rv32iProgramRetirements state program) := by
  induction certificate with
  | nil start state => exact .nil start
  | bubble hvalid tail ih => exact .bubble hvalid ih
  | retire horder boundary tail ih =>
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      exact .retire hspec.1 horder hretirement ih

theorem Rv32iRvfiTrace.normalize
    {memory : Memory} {start : Nat} {state : RvMemoryState}
    {observations : List RvfiObservation} {program : List Rv32iInstruction}
    (certificate : Rv32iRvfiTrace memory start state observations program) :
    normalizeRvfiTrace? start observations =
      some (rv32iProgramRetirements state program) :=
  (normalizeRvfiTrace?_iff).2 certificate.toRvfiTraceRefines

theorem Rv32iRvfiTrace.trace_refines
    (profile : PlatformProfile)
    {memory : Memory} {start : Nat} {state : RvMemoryState}
    {observations : List RvfiObservation} {program : List Rv32iInstruction}
    (certificate : Rv32iRvfiTrace memory start state observations program) :
    normalizeRvfiTrace? start observations =
      some (trace (rvMemoryMachineWith profile) state
        (rv32iProgramInputs state program)) := by
  calc
    normalizeRvfiTrace? start observations =
        some (rv32iProgramRetirements state program) := certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile) state
        (rv32iProgramInputs state program)) := by
      rw [rvMemoryMachineWith_rv32i_program_trace]

theorem Rv32iRvfiTrace.append
    {memory : Memory} {start : Nat} {state : RvMemoryState}
    {firstObservations secondObservations : List RvfiObservation}
    {firstProgram secondProgram : List Rv32iInstruction}
    (first : Rv32iRvfiTrace memory start state firstObservations firstProgram)
    (second : Rv32iRvfiTrace memory
      (start + firstProgram.length)
      (rv32iProgramState state firstProgram)
      secondObservations secondProgram) :
    Rv32iRvfiTrace memory start state
      (firstObservations ++ secondObservations)
      (firstProgram ++ secondProgram) := by
  induction first with
  | nil start state =>
      simpa [rv32iProgramState] using second
  | bubble hvalid tail ih =>
      refine Rv32iRvfiTrace.bubble hvalid ?_
      apply ih
      simpa [rv32iProgramState] using second
  | retire horder boundary tail ih =>
      refine Rv32iRvfiTrace.retire horder boundary ?_
      apply ih
      simpa [rv32iProgramState, List.length_cons, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using second

/-! ## Input-aware cycle certificate -/

/-- A mixed RV32I certificate tied to an actual packed-RVFI cycle machine. -/
inductive Rv32iRvfiCycleTrace {State : Type}
    (machine : RvfiCycleMachine State) :
    Nat → State → RvMemoryState → List Input → List Rv32iInstruction → Prop where
  | nil (start : Nat) (coreState : State) (state : RvMemoryState) :
      Rv32iRvfiCycleTrace machine start coreState state [] []
  | bubble {start : Nat} {coreState coreState' : State}
      {state : RvMemoryState} {cycleInput : Input} {cycles : List Input}
      {program : List Rv32iInstruction} {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hvalid : observation.valid = false)
      (tail : Rv32iRvfiCycleTrace machine (start) coreState' state cycles program) :
      Rv32iRvfiCycleTrace machine start coreState state
        (cycleInput :: cycles) program
  | retire {start : Nat} {coreState coreState' : State}
      {state : RvMemoryState} {cycleInput : Input} {cycles : List Input}
      {instruction : Rv32iInstruction} {program : List Rv32iInstruction}
      {observation : RvfiObservation}
      (hstep : machine.step coreState cycleInput = (coreState', observation))
      (hinput : cycleInput = rv32iProgramInput state instruction)
      (horder : observation.order = start)
      (boundary :
        Rv32iBoundary state.arch (rv32iProgramInput state instruction) observation
          (rv32iProgramStep state instruction) (rv32iProgramRetirement state instruction))
      (tail : Rv32iRvfiCycleTrace machine (start + 1) coreState'
        (rv32iProgramStep state instruction) cycles program) :
      Rv32iRvfiCycleTrace machine start coreState state
        (cycleInput :: cycles) (instruction :: program)

/-- An ordered mixed step invariant constructs a certificate for every finite
cycle window.  The resulting program is the exact sequence of valid rows;
bubbles retain their inputs and core transitions, and the final relation is
threaded to the mixed architectural state. -/
theorem rv32iRvfiCycleTrace_of_step
    {State : Type} (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hstep : Rv32iCycleStepRefines machine rel admit)
    (start : Nat) (coreState : State) (memoryState : RvMemoryState)
    (cycles : List Input) (hrel : rel coreState memoryState)
    (hall : ∀ input ∈ cycles, admit input) :
    ∃ program : List Rv32iInstruction,
      Rv32iRvfiCycleTrace machine start coreState memoryState cycles program ∧
      rel (rvfiStateAfter machine coreState cycles)
        (rv32iProgramState memoryState program) := by
  induction cycles generalizing start coreState memoryState with
  | nil =>
      refine ⟨[], .nil start coreState memoryState, ?_⟩
      simpa [rvfiStateAfter, rv32iProgramState] using hrel
  | cons input cycles ih =>
      have hadmit : admit input := hall input (by simp)
      have htail : ∀ input' ∈ cycles, admit input' := by
        intro input' hmem
        exact hall input' (by simp [hmem])
      have hcase := hstep start coreState memoryState input hrel hadmit
      cases hmachine : machine.step coreState input with
      | mk coreState' observation =>
          simp only [hmachine] at hcase
          by_cases hv : observation.valid = true
          · have hcase' : ∃ instruction,
                input = rv32iProgramInput memoryState instruction ∧
                observation.order = start ∧
                Rv32iBoundary memoryState.arch input observation
                  (rv32iProgramStep memoryState instruction)
                  (rv32iProgramRetirement memoryState instruction) ∧
                rel coreState' (rv32iProgramStep memoryState instruction) := by
              simpa [hv] using hcase
            rcases hcase' with
              ⟨instruction, hinput, horder, hboundary, hrel'⟩
            obtain ⟨program, htrace, hfinal⟩ :=
              ih (start := start + 1) (coreState := coreState')
                (memoryState := rv32iProgramStep memoryState instruction)
                hrel' htail
            have hboundary' :
                Rv32iBoundary memoryState.arch
                  (rv32iProgramInput memoryState instruction) observation
                  (rv32iProgramStep memoryState instruction)
                  (rv32iProgramRetirement memoryState instruction) := by
              simpa [hinput] using hboundary
            refine ⟨instruction :: program, ?_, ?_⟩
            · exact .retire hmachine hinput horder hboundary' htrace
            · simpa [rvfiStateAfter, rv32iProgramState, hmachine] using hfinal
          · have hv' : observation.valid = false := by
              cases hvalue : observation.valid with
              | false => exact rfl
              | true => exact False.elim (hv hvalue)
            have hrel' : rel coreState' memoryState := by
              simpa [hv, hv'] using hcase
            obtain ⟨program, htrace, hfinal⟩ :=
              ih (start := start) (coreState := coreState')
                (memoryState := memoryState) hrel' htail
            refine ⟨program, ?_, ?_⟩
            · exact .bubble hmachine hv' htrace
            · simpa [rvfiStateAfter, hmachine] using hfinal

theorem Rv32iRvfiCycleTrace.normalize
    {State : Type} {machine : RvfiCycleMachine State}
    {start : Nat} {coreState : State} {state : RvMemoryState}
    {cycles : List Input} {program : List Rv32iInstruction}
    (certificate : Rv32iRvfiCycleTrace machine start coreState state cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (rv32iProgramRetirements state program) := by
  induction certificate with
  | nil start coreState state => rfl
  | bubble hstep hvalid tail ih =>
      simp only [rvfiObservations, hstep]
      simp [normalizeRvfiTrace?, hvalid, ih]
  | retire hstep hinput horder boundary tail ih =>
      simp only [rvfiObservations, hstep]
      have hspec := boundary.observation_spec
      have hretirement := boundary.toRetirement?_eq_some
      simp [normalizeRvfiTrace?, rv32iProgramRetirements, hspec.1,
        horder, hretirement, ih]

theorem Rv32iRvfiCycleTrace.retireInputs_eq
    {State : Type} {machine : RvfiCycleMachine State}
    {start : Nat} {coreState : State} {state : RvMemoryState}
    {cycles : List Input} {program : List Rv32iInstruction}
    (certificate : Rv32iRvfiCycleTrace machine start coreState state cycles program) :
    retireInputs machine.toCycleMachine coreState cycles =
      rv32iProgramInputs state program := by
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
      have hretirement := boundary.toRetirement?_eq_some
      have hstep' :
          machine.toCycleMachine.step coreState cycleInput =
            (coreState', some (rv32iProgramRetirement state instruction)) := by
        simp [RvfiCycleMachine.toCycleMachine, hstep, hretirement]
      simp only [retireInputs, hstep']
      rw [hinput]
      simpa [rv32iProgramInputs] using ih

theorem Rv32iRvfiCycleTrace.trace_refines
    {State : Type} (profile : PlatformProfile)
    {machine : RvfiCycleMachine State}
    {start : Nat} {coreState : State} {state : RvMemoryState}
    {cycles : List Input} {program : List Rv32iInstruction}
    (certificate : Rv32iRvfiCycleTrace machine start coreState state cycles program) :
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
      some (trace (rvMemoryMachineWith profile) state
        (retireInputs machine.toCycleMachine coreState cycles)) := by
  calc
    normalizeRvfiTrace? start (rvfiObservations machine coreState cycles) =
        some (rv32iProgramRetirements state program) := certificate.normalize
    _ = some (trace (rvMemoryMachineWith profile) state
        (rv32iProgramInputs state program)) := by
      rw [rvMemoryMachineWith_rv32i_program_trace]
    _ = some (trace (rvMemoryMachineWith profile) state
        (retireInputs machine.toCycleMachine coreState cycles)) := by
      rw [certificate.retireInputs_eq]

/-- The mixed step invariant and a finite-window admission proof compose
directly to the normalized stateful ISA trace and the final relation. -/
theorem rv32iRvfiCycleTrace_of_step_refines
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hstep : Rv32iCycleStepRefines machine rel admit)
    (start : Nat) (coreState : State) (memoryState : RvMemoryState)
    (cycles : List Input) (hrel : rel coreState memoryState)
    (hall : ∀ input ∈ cycles, admit input) :
    ∃ program : List Rv32iInstruction,
      ∃ _certificate :
        Rv32iRvfiCycleTrace machine start coreState memoryState cycles program,
        normalizeRvfiTrace? start
            (rvfiObservations machine coreState cycles) =
          some (trace (rvMemoryMachineWith profile) memoryState
            (retireInputs machine.toCycleMachine coreState cycles)) ∧
        rel (rvfiStateAfter machine coreState cycles)
          (rv32iProgramState memoryState program) := by
  obtain ⟨program, certificate, hfinal⟩ := rv32iRvfiCycleTrace_of_step
    machine rel admit hstep start coreState memoryState cycles hrel hall
  exact ⟨program, certificate, certificate.trace_refines profile, hfinal⟩

theorem Rv32iRvfiCycleTrace.append
    {State : Type} {machine : RvfiCycleMachine State}
    {start : Nat} {coreState : State} {state : RvMemoryState}
    {firstCycles secondCycles : List Input}
    {firstProgram secondProgram : List Rv32iInstruction}
    (first : Rv32iRvfiCycleTrace machine start coreState state
      firstCycles firstProgram)
    (second : Rv32iRvfiCycleTrace machine
      (start + firstProgram.length)
      (rvfiStateAfter machine coreState firstCycles)
      (rv32iProgramState state firstProgram)
      secondCycles secondProgram) :
    Rv32iRvfiCycleTrace machine start coreState state
      (firstCycles ++ secondCycles) (firstProgram ++ secondProgram) := by
  induction first with
  | nil start coreState state =>
      simpa [rvfiStateAfter, rv32iProgramState] using second
  | bubble hstep hvalid tail ih =>
      refine Rv32iRvfiCycleTrace.bubble hstep hvalid ?_
      apply ih
      simpa [rvfiStateAfter, hstep] using second
  | retire hstep hinput horder boundary tail ih =>
      refine Rv32iRvfiCycleTrace.retire hstep hinput horder boundary ?_
      apply ih
      simpa [rvfiStateAfter, rv32iProgramState, hstep, List.length_cons,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using second

#print axioms LeanModels.Refine.rv32iProgramInputs_append
#print axioms LeanModels.Refine.rv32iProgramState_append
#print axioms LeanModels.Refine.rv32iProgramRetirements_append
#print axioms LeanModels.Refine.Rv32iInstruction.decode_word
#print axioms LeanModels.Refine.rv32iProgramInput_fetched
#print axioms LeanModels.Refine.rvMemoryMachineWith_rv32i_step
#print axioms LeanModels.Refine.rvMemoryMachineWith_rv32i_program_state
#print axioms LeanModels.Refine.rvMemoryStateAfter_rv32i_program
#print axioms LeanModels.Refine.rvMemoryMachineWith_rv32i_program_trace
#print axioms LeanModels.Refine.rvfiCycleStepRefines_of_rv32i_program
#print axioms LeanModels.Refine.rv32iRvfiCycleTrace_of_step
#print axioms LeanModels.Refine.rv32iRvfiCycleTrace_of_step_refines
#print axioms LeanModels.Refine.Rv32iRvfiTrace.toRvfiTraceRefines
#print axioms LeanModels.Refine.Rv32iRvfiTrace.normalize
#print axioms LeanModels.Refine.Rv32iRvfiTrace.trace_refines
#print axioms LeanModels.Refine.Rv32iRvfiTrace.append
#print axioms LeanModels.Refine.Rv32iRvfiCycleTrace.normalize
#print axioms LeanModels.Refine.Rv32iRvfiCycleTrace.retireInputs_eq
#print axioms LeanModels.Refine.Rv32iRvfiCycleTrace.trace_refines
#print axioms LeanModels.Refine.Rv32iRvfiCycleTrace.append

end LeanModels.Refine
