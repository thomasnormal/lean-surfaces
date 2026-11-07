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

/-! ## Lifting an ADDI invariant to the mixed per-cycle obligation -/

/-- An order-aware, memory-threaded ADDI invariant discharges the unified
mixed RV32I cycle obligation.

The extra order premise is explicit because `RvfiCycleStepRefines` is the
raw strict contract, while `Rv32iCycleStepRefines` also indexes each valid
row by its retirement order.  The proof constructs the decoded
`AddiInstruction` from the boundary's parser-derived decode equality, then
uses the instruction embedding above; no row or input is reconstructed from
a captured trace.
-/
theorem rv32iCycleStepRefines_of_addi_memory
    {State : Type}
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hstep : ∀ (state : State) (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ w rd rs1 imm,
          input.memory = memoryState.memory ∧
          observation.addiBoundary memoryState.arch input w rd rs1 imm ∧
          rel state'
            { arch := addiNext memoryState.arch rd rs1 imm,
              memory := memoryState.memory }
      else rel state' memoryState)
    (horder : ∀ (start : Nat) (state : State)
      (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (_, observation) := machine.step state input
      if observation.valid then observation.order = start else True) :
    Rv32iCycleStepRefines machine rel admit := by
  intro start state memoryState input hrel hadmit
  have hcase := hstep state memoryState input hrel hadmit
  have horderCase := horder start state memoryState input hrel hadmit
  rcases hmachine : machine.step state input with ⟨state', observation⟩
  simp only [hmachine] at hcase horderCase ⊢
  by_cases hv : observation.valid = true
  · have hcase' : ∃ w rd rs1 imm,
        input.memory = memoryState.memory ∧
        observation.addiBoundary memoryState.arch input w rd rs1 imm ∧
        rel state'
          { arch := addiNext memoryState.arch rd rs1 imm,
            memory := memoryState.memory } := by
      simpa [hv] using hcase
    rcases hcase' with ⟨w, rd, rs1, imm, hmem, hboundary, hrel'⟩
    have horder' : observation.order = start := by
      simpa [hv] using horderCase
    have hdecode : Fetched.decode (.word w) =
        some (.alu .add rd (.reg rs1) (.imm imm)) :=
      hboundary.1.2.2.1
    let instruction : AddiInstruction :=
      { word := w, rd := rd, rs1 := rs1, imm := imm, decode := hdecode }
    have hinput : input = addiProgramInput memoryState.memory instruction := by
      cases input with
      | mk fetched memory irq =>
          have hfetched : fetched = .word w := by
            simpa using hboundary.1.2.1
          have hirq : irq = 0 := by
            simpa using hboundary.1.1
          cases hfetched
          cases hmem
          cases hirq
          rfl
    have hboundaryAlu :=
      RvfiObservation.addiBoundary_rv32i w rd rs1 imm hboundary
    have hboundary' :
        Rv32iBoundary memoryState.arch
          input observation
          (rv32iProgramStep memoryState instruction.toRv32i)
          (rv32iProgramRetirement memoryState instruction.toRv32i) := by
      rw [addi_toRv32i_step, addi_toRv32i_retirement]
      rw [← hinput]
      simpa [instruction, AddiInstruction.toAlu, addiNext, aluNext,
        addiRetirement, aluRetirement, addiEffects, aluEffects, src1Val,
        src2Val, aluSem, hmem] using
        hboundaryAlu
    simp only [hv]
    refine ⟨instruction.toRv32i, ?_, horder', hboundary', ?_⟩
    · rw [hinput]
      exact addi_toRv32i_input memoryState instruction
    · rw [addi_toRv32i_step]
      exact hrel'
  · have hv' : observation.valid = false := by
      cases hvalue : observation.valid with
      | false => exact rfl
      | true => exact False.elim (hv hvalue)
    have hrel' : rel state' memoryState := by
      simpa [hv, hv'] using hcase
    simp only [hv]
    exact hrel'

#print axioms LeanModels.Refine.addi_toRv32i_input
#print axioms LeanModels.Refine.addi_toRv32i_step
#print axioms LeanModels.Refine.addi_toRv32i_retirement
#print axioms LeanModels.Refine.AddiRvfiCycleTrace.toRv32i
#print axioms LeanModels.Refine.AddiRvfiCycleTrace.toRv32i_trace_refines
#print axioms LeanModels.Refine.rv32iCycleStepRefines_of_addi_memory

end LeanModels.Refine
