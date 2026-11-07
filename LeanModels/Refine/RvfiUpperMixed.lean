import LeanModels.Refine.RvfiUpperProgram
import LeanModels.Refine.RvfiRv32iProgram

/-!
# Embedding upper-immediate certificates in the mixed RV32I surface

`RvfiUpperProgram` carries LUI and AUIPC certificates as one upper-immediate
family.  The mixed RV32I certificate consumes the same rows through its ALU
constructor, so this file supplies the structure-preserving adapter without
re-decoding words or reconstructing cycle inputs.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## The instruction embedding -/

/-- The mixed ALU instruction represented by one LUI or AUIPC. -/
def UpperInstruction.toAlu (instruction : UpperInstruction) : AluInstruction :=
  match instruction with
  | ⟨word, .lui rd imm, decode⟩ =>
      { word := word
        op := .add
        rd := rd
        src1 := .reg 0
        src2 := .imm imm
        decode := by
          simpa [UpperKind.toInstr] using decode }
  | ⟨word, .auipc rd imm, decode⟩ =>
      { word := word
        op := .add
        rd := rd
        src1 := .pc
        src2 := .imm imm
        decode := by
          simpa [UpperKind.toInstr] using decode }

/-- The unified RV32I instruction represented by one upper-immediate. -/
def UpperInstruction.toRv32i (instruction : UpperInstruction) :
    Rv32iInstruction :=
  .alu instruction.toAlu

/-- The raw RVFI boundary selected by one decoded upper-immediate. -/
def RvfiObservation.upperBoundary (s : ArchState) (input : Input)
    (o : RvfiObservation) (instruction : UpperInstruction) : Prop :=
  match instruction.kind with
  | .lui rd imm => o.luiBoundary s input instruction.word rd imm
  | .auipc rd imm => o.auipcBoundary s input instruction.word rd imm

theorem RvfiObservation.upperBoundary_input
    {s : ArchState} {input : Input} {o : RvfiObservation}
    (instruction : UpperInstruction)
    (h : o.upperBoundary s input instruction) :
    input = upperProgramInput input.memory instruction := by
  cases instruction with
  | mk word kind decode =>
      cases kind with
      | lui rd imm =>
          have hirq : input.irq = 0 := h.1.1
          have hfetched : input.fetched = .word word := h.1.2.1
          cases input with
          | mk fetched memory irq =>
              simp_all [upperProgramInput]
      | auipc rd imm =>
          have hirq : input.irq = 0 := h.1.1
          have hfetched : input.fetched = .word word := h.1.2.1
          cases input with
          | mk fetched memory irq =>
              simp_all [upperProgramInput]

theorem RvfiObservation.upperBoundary_rv32i
    {s : ArchState} {input : Input} {o : RvfiObservation}
    (instruction : UpperInstruction)
    (h : o.upperBoundary s input instruction) :
    Rv32iBoundary s input o
      { arch := UpperKind.next s instruction.kind,
        memory := input.memory }
      (UpperKind.retirement s input instruction.kind) := by
  cases instruction with
  | mk word kind decode =>
      cases kind with
      | lui rd imm =>
          simpa [RvfiObservation.upperBoundary, UpperKind.next,
            UpperKind.retirement, luiNext, aluNext, luiRetirement,
            aluRetirement, luiEffects, aluEffects, src1Val, src2Val,
            aluSem] using
            (RvfiObservation.luiBoundary_rv32i word rd imm h)
      | auipc rd imm =>
          simpa [RvfiObservation.upperBoundary, UpperKind.next,
            UpperKind.retirement, auipcNext, aluNext, auipcRetirement,
            aluRetirement, auipcEffects, aluEffects, src1Val, src2Val,
            aluSem] using
            (RvfiObservation.auipcBoundary_rv32i word rd imm h)

theorem upper_toRv32i_input (state : RvMemoryState)
    (instruction : UpperInstruction) :
    rv32iProgramInput state instruction.toRv32i =
      upperProgramInput state.memory instruction := by
  cases instruction with
  | mk word kind decode =>
      cases kind <;> rfl

theorem upper_toRv32i_step (state : RvMemoryState)
    (instruction : UpperInstruction) :
    rv32iProgramStep state instruction.toRv32i =
      { arch := UpperKind.next state.arch instruction.kind,
        memory := state.memory } := by
  cases instruction with
  | mk word kind decode =>
      cases kind <;>
        simp [UpperInstruction.toRv32i, UpperInstruction.toAlu,
          rv32iProgramStep, UpperKind.next, luiNext, auipcNext,
          aluNext, src1Val, src2Val, aluSem]

theorem upper_toRv32i_retirement (state : RvMemoryState)
    (instruction : UpperInstruction) :
    rv32iProgramRetirement state instruction.toRv32i =
      UpperKind.retirement state.arch
        (upperProgramInput state.memory instruction) instruction.kind := by
  cases instruction with
  | mk word kind decode =>
      cases kind <;> rfl

/-! ## The cycle-certificate adapter -/

/-- An input-aware upper-immediate certificate is a mixed RV32I certificate
over the same cycles and core states. -/
theorem UpperRvfiCycleTrace.toRv32i
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List UpperInstruction}
    (certificate : UpperRvfiCycleTrace machine memory start coreState state
      cycles program) :
    Rv32iRvfiCycleTrace machine start coreState
      { arch := state, memory := memory } cycles
      (program.map UpperInstruction.toRv32i) := by
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
      · simpa [upper_toRv32i_input] using hinput
      · have hinput' := upper_toRv32i_input
          ({ arch := state, memory := memory } : RvMemoryState) instruction
        have hstep' := upper_toRv32i_step
          ({ arch := state, memory := memory } : RvMemoryState) instruction
        have hretirement' := upper_toRv32i_retirement
          ({ arch := state, memory := memory } : RvMemoryState) instruction
        rw [hinput', hstep', hretirement']
        exact boundary
      · simpa [upper_toRv32i_step] using ih

theorem UpperRvfiCycleTrace.toRv32i_trace_refines
    {State : Type} (profile : PlatformProfile)
    {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List UpperInstruction}
    (certificate : UpperRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start
        (rvfiObservations machine coreState cycles) =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
  exact certificate.toRv32i.trace_refines profile

/-! ## Lifting an upper-immediate invariant to the mixed per-cycle obligation -/

/-- An order-aware, memory-threaded upper-immediate invariant discharges the
unified mixed RV32I cycle obligation.  The instruction witness retains its
decoder proof and selects either the exact LUI or AUIPC boundary. -/
theorem rv32iCycleStepRefines_of_upper_memory
    {State : Type}
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hstep : ∀ (state : State) (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ instruction : UpperInstruction,
          input.memory = memoryState.memory ∧
          observation.upperBoundary memoryState.arch input instruction ∧
          rel state'
            { arch := UpperKind.next memoryState.arch instruction.kind,
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
  · have hcase' : ∃ instruction : UpperInstruction,
        input.memory = memoryState.memory ∧
        observation.upperBoundary memoryState.arch input instruction ∧
        rel state'
          { arch := UpperKind.next memoryState.arch instruction.kind,
            memory := memoryState.memory } := by
      simpa [hv] using hcase
    rcases hcase' with ⟨instruction, hmem, hboundary, hrel'⟩
    have horder' : observation.order = start := by
      simpa [hv] using horderCase
    have hinput : input = upperProgramInput memoryState.memory instruction := by
      have hinput' := RvfiObservation.upperBoundary_input instruction hboundary
      rw [hmem] at hinput'
      exact hinput'
    have hboundary' :
        Rv32iBoundary memoryState.arch
          input observation
          (rv32iProgramStep memoryState instruction.toRv32i)
          (rv32iProgramRetirement memoryState instruction.toRv32i) := by
      rw [upper_toRv32i_step, upper_toRv32i_retirement]
      rw [← hinput]
      simpa [hmem] using
        (RvfiObservation.upperBoundary_rv32i instruction hboundary)
    simp only [hv]
    refine ⟨instruction.toRv32i, ?_, horder', hboundary', ?_⟩
    · calc
        input = upperProgramInput memoryState.memory instruction := hinput
        _ = rv32iProgramInput memoryState instruction.toRv32i :=
          (upper_toRv32i_input memoryState instruction).symm
    · rw [upper_toRv32i_step]
      exact hrel'
  · have hv' : observation.valid = false := by
      cases hvalue : observation.valid with
      | false => exact rfl
      | true => exact False.elim (hv hvalue)
    have hrel' : rel state' memoryState := by
      simpa [hv, hv'] using hcase
    simp only [hv]
    exact hrel'

#print axioms LeanModels.Refine.RvfiObservation.upperBoundary
#print axioms LeanModels.Refine.RvfiObservation.upperBoundary_input
#print axioms LeanModels.Refine.RvfiObservation.upperBoundary_rv32i
#print axioms LeanModels.Refine.rv32iCycleStepRefines_of_upper_memory
#print axioms LeanModels.Refine.UpperInstruction.toAlu
#print axioms LeanModels.Refine.UpperInstruction.toRv32i
#print axioms LeanModels.Refine.upper_toRv32i_input
#print axioms LeanModels.Refine.upper_toRv32i_step
#print axioms LeanModels.Refine.upper_toRv32i_retirement
#print axioms LeanModels.Refine.UpperRvfiCycleTrace.toRv32i
#print axioms LeanModels.Refine.UpperRvfiCycleTrace.toRv32i_trace_refines

end LeanModels.Refine
