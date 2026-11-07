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

#print axioms LeanModels.Refine.UpperInstruction.toAlu
#print axioms LeanModels.Refine.UpperInstruction.toRv32i
#print axioms LeanModels.Refine.upper_toRv32i_input
#print axioms LeanModels.Refine.upper_toRv32i_step
#print axioms LeanModels.Refine.upper_toRv32i_retirement
#print axioms LeanModels.Refine.UpperRvfiCycleTrace.toRv32i
#print axioms LeanModels.Refine.UpperRvfiCycleTrace.toRv32i_trace_refines

end LeanModels.Refine
