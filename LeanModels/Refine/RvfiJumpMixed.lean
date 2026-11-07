import LeanModels.Refine.RvfiJumpProgram
import LeanModels.Refine.RvfiRv32iProgram

/-!
# Embedding jump certificates in the mixed RV32I surface

`RvfiJumpProgram` carries JAL and JALR certificates as one jump family.  The
mixed RV32I certificate already has a corresponding `.jump` constructor, so
this file provides the structure-preserving adapter without re-decoding words
or reconstructing cycle inputs.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## The instruction embedding -/

/-- The unified RV32I instruction represented by one JAL or JALR. -/
def JumpInstruction.toRv32i (instruction : JumpInstruction) :
    Rv32iInstruction :=
  .jump instruction

/-- The raw RVFI boundary selected by one decoded jump instruction. -/
def RvfiObservation.jumpBoundary (s : ArchState) (input : Input)
    (o : RvfiObservation) (instruction : JumpInstruction) : Prop :=
  match instruction.kind with
  | .jal rd offset => o.jalBoundary s input instruction.word rd offset
  | .jalr rd rs1 offset =>
      o.jalrBoundary s input instruction.word rd rs1 offset

theorem RvfiObservation.jumpBoundary_input
    {s : ArchState} {input : Input} {o : RvfiObservation}
    (instruction : JumpInstruction)
    (h : o.jumpBoundary s input instruction) :
    input = jumpProgramInput input.memory instruction := by
  cases instruction with
  | mk word kind decode =>
      cases kind with
      | jal rd offset =>
          have hirq : input.irq = 0 := h.1.1
          have hfetched : input.fetched = .word word := h.1.2.1
          cases input with
          | mk fetched memory irq =>
              simp_all [jumpProgramInput]
      | jalr rd rs1 offset =>
          have hirq : input.irq = 0 := h.1.1
          have hfetched : input.fetched = .word word := h.1.2.1
          cases input with
          | mk fetched memory irq =>
              simp_all [jumpProgramInput]

theorem RvfiObservation.jumpBoundary_rv32i
    {s : ArchState} {input : Input} {o : RvfiObservation}
    (instruction : JumpInstruction)
    (h : o.jumpBoundary s input instruction) :
    Rv32iBoundary s input o
      { arch := JumpKind.next s instruction.kind,
        memory := input.memory }
      (JumpKind.retirement s input instruction.kind) := by
  cases instruction with
  | mk word kind decode =>
      cases kind with
      | jal rd offset =>
          simpa [RvfiObservation.jumpBoundary, JumpKind.next,
            JumpKind.retirement] using
            (RvfiObservation.jalBoundary_rv32i word rd offset h)
      | jalr rd rs1 offset =>
          simpa [RvfiObservation.jumpBoundary, JumpKind.next,
            JumpKind.retirement] using
            (RvfiObservation.jalrBoundary_rv32i word rd rs1 offset h)

theorem jump_toRv32i_input (state : RvMemoryState)
    (instruction : JumpInstruction) :
    rv32iProgramInput state instruction.toRv32i =
      jumpProgramInput state.memory instruction := by
  rfl

theorem jump_toRv32i_step (state : RvMemoryState)
    (instruction : JumpInstruction) :
    rv32iProgramStep state instruction.toRv32i =
      { arch := JumpKind.next state.arch instruction.kind,
        memory := state.memory } := by
  rfl

theorem jump_toRv32i_retirement (state : RvMemoryState)
    (instruction : JumpInstruction) :
    rv32iProgramRetirement state instruction.toRv32i =
      JumpKind.retirement state.arch
        (jumpProgramInput state.memory instruction) instruction.kind := by
  rfl

/-! ## The cycle-certificate adapter -/

/-- An input-aware jump certificate is a mixed RV32I certificate over the
same cycles and core states. -/
theorem JumpRvfiCycleTrace.toRv32i
    {State : Type} {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List JumpInstruction}
    (certificate : JumpRvfiCycleTrace machine memory start coreState state
      cycles program) :
    Rv32iRvfiCycleTrace machine start coreState
      { arch := state, memory := memory } cycles
      (program.map JumpInstruction.toRv32i) := by
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
      · simpa [jump_toRv32i_input] using hinput
      · have hinput' := jump_toRv32i_input
          ({ arch := state, memory := memory } : RvMemoryState) instruction
        have hstep' := jump_toRv32i_step
          ({ arch := state, memory := memory } : RvMemoryState) instruction
        have hretirement' := jump_toRv32i_retirement
          ({ arch := state, memory := memory } : RvMemoryState) instruction
        rw [hinput', hstep', hretirement']
        exact boundary
      · simpa [jump_toRv32i_step] using ih

theorem JumpRvfiCycleTrace.toRv32i_trace_refines
    {State : Type} (profile : PlatformProfile)
    {machine : RvfiCycleMachine State} {memory : Memory}
    {start : Nat} {coreState : State} {state : ArchState}
    {cycles : List Input} {program : List JumpInstruction}
    (certificate : JumpRvfiCycleTrace machine memory start coreState state
      cycles program) :
    normalizeRvfiTrace? start
        (rvfiObservations machine coreState cycles) =
      some (trace (rvMemoryMachineWith profile)
        { arch := state, memory := memory }
        (retireInputs machine.toCycleMachine coreState cycles)) := by
  exact certificate.toRv32i.trace_refines profile

#print axioms LeanModels.Refine.JumpInstruction.toRv32i
#print axioms LeanModels.Refine.RvfiObservation.jumpBoundary
#print axioms LeanModels.Refine.RvfiObservation.jumpBoundary_input
#print axioms LeanModels.Refine.RvfiObservation.jumpBoundary_rv32i
#print axioms LeanModels.Refine.jump_toRv32i_input
#print axioms LeanModels.Refine.jump_toRv32i_step
#print axioms LeanModels.Refine.jump_toRv32i_retirement
#print axioms LeanModels.Refine.JumpRvfiCycleTrace.toRv32i
#print axioms LeanModels.Refine.JumpRvfiCycleTrace.toRv32i_trace_refines

end LeanModels.Refine
