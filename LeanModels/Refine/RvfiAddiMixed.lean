import LeanModels.Refine.RvfiAddiProgram
import LeanModels.Refine.RvfiRv32iProgram

/-!
# Embedding ADDI certificates in the mixed RV32I surface

`RvfiAddiProgram` predates the unified mixed instruction certificate and is
useful for proving the first instruction-class invariant in isolation.  A
loaded-core proof must eventually consume that result through
`Rv32iRvfiCycleTrace`, however.  This file gives the structure-preserving
adapter: an ADDI instruction becomes the corresponding `.alu` instruction,
and an input-aware ADDI cycle certificate becomes the mixed certificate over
the same cycles.

The adapter does not reinterpret observations or reconstruct inputs.  It
retains each ADDI decoder proof and reuses the original boundary proof at the
same cycle and architectural state.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## The instruction embedding -/

/-- The mixed ALU instruction represented by one decoded ADDI. -/
def AddiInstruction.toAlu (instruction : AddiInstruction) : AluInstruction :=
  { word := instruction.word
    op := .add
    rd := instruction.rd
    src1 := .reg instruction.rs1
    src2 := .imm instruction.imm
    decode := instruction.decode }

/-- The unified RV32I instruction represented by one decoded ADDI. -/
def AddiInstruction.toRv32i (instruction : AddiInstruction) :
    Rv32iInstruction :=
  .alu instruction.toAlu

theorem addi_toRv32i_input (state : RvMemoryState)
    (instruction : AddiInstruction) :
    rv32iProgramInput state instruction.toRv32i =
      addiProgramInput state.memory instruction := by
  rfl

theorem addi_toRv32i_step (state : RvMemoryState)
    (instruction : AddiInstruction) :
    rv32iProgramStep state instruction.toRv32i =
      { arch := addiNext state.arch instruction.rd instruction.rs1
          instruction.imm
        memory := state.memory } := by
  simp [AddiInstruction.toRv32i, AddiInstruction.toAlu, rv32iProgramStep,
    addiNext, aluNext, src1Val, src2Val, aluSem]

theorem addi_toRv32i_retirement (state : RvMemoryState)
    (instruction : AddiInstruction) :
    rv32iProgramRetirement state instruction.toRv32i =
      addiRetirement state.arch
        (addiProgramInput state.memory instruction)
        instruction.rd instruction.rs1 instruction.imm := by
  rfl

/-! ## The cycle-certificate adapter -/

/-- An input-aware ADDI certificate is a mixed RV32I certificate over the
same cycles and core states. -/
theorem AddiRvfiCycleTrace.toRv32i
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List AddiInstruction}
    (certificate : AddiRvfiCycleTrace machine memory start coreState state
      cycles program) :
    Rv32iRvfiCycleTrace machine start coreState
      { arch := state, memory := memory } cycles
      (program.map AddiInstruction.toRv32i) := by
  induction certificate with
  | nil start coreState state =>
      exact .nil start coreState { arch := state, memory := memory }
  | @bubble start coreState coreState' state cycleInput cycles program
      observation hstep hvalid tail ih =>
      refine .bubble hstep hvalid ?_
      simpa using ih
  | @retire start coreState coreState' state cycleInput cycles
      instruction program observation hstep hinput horder boundary tail ih =>
      refine .retire hstep ?_ horder ?_ ?_
      · simpa [addi_toRv32i_input] using hinput
      · have hinput' := addi_toRv32i_input
          ({ arch := state, memory := memory } : RvMemoryState) instruction
        have hstep' := addi_toRv32i_step
          ({ arch := state, memory := memory } : RvMemoryState) instruction
        have hretirement' := addi_toRv32i_retirement
          ({ arch := state, memory := memory } : RvMemoryState) instruction
        rw [hinput', hstep', hretirement']
        exact boundary
      · simpa [addi_toRv32i_step] using ih

theorem AddiRvfiCycleTrace.toRv32i_trace_refines
    {State : Type} (profile : PlatformProfile)
    {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List AddiInstruction}
    (certificate : AddiRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start
        (rvfiObservations machine coreState cycles) =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
  exact certificate.toRv32i.trace_refines profile

#print axioms LeanModels.Refine.addi_toRv32i_input
#print axioms LeanModels.Refine.addi_toRv32i_step
#print axioms LeanModels.Refine.addi_toRv32i_retirement
#print axioms LeanModels.Refine.AddiRvfiCycleTrace.toRv32i
#print axioms LeanModels.Refine.AddiRvfiCycleTrace.toRv32i_trace_refines

end LeanModels.Refine
