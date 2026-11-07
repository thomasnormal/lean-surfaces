import LeanModels.Refine.RvfiMem
import LeanModels.Refine.Rv32iAlu

/-!
# Raw RVFI ALU boundary

This is the generic raw contract for the ISA model's `.alu` constructor.  It
covers register-register and immediate operations, as well as pc-based forms;
the specialized ADDI/LUI/AUIPC predicates remain useful when a core proof wants
the source fields named directly.  Immediate source fields are deliberately
left unconstrained because RVFI does not assign them architectural meaning.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-- The raw RVFI facts for a 32-bit ALU instruction. -/
def RvfiObservation.aluFields (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (op : AluOp) (rd : Reg)
    (src1 : Src1) (src2 : Src2) : Prop :=
  input.irq = 0 ∧
  input.fetched = .word w ∧
  Fetched.decode (.word w) = some (.alu op rd src1 src2) ∧
  o.valid = true ∧
  o.wellFormed ∧
  o.insn = w ∧
  o.pcRdata = s.pc ∧
  o.pcWdata = s.pc + 4 ∧
  aluSrc1Fields s o src1 ∧
  aluSrc2Fields s o src2 ∧
  o.rdAddr = rd ∧
  o.rdWdata = aluSem op (src1Val s src1) (src2Val s src2) ∧
  o.trap = false ∧
  o.intr = false ∧
  o.memRmask = 0 ∧
  o.memWmask = 0 ∧
  o.cause = none

def RvfiObservation.aluBoundary (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (op : AluOp) (rd : Reg)
    (src1 : Src1) (src2 : Src2) : Prop :=
  o.aluFields s input w op rd src1 src2 ∧
  o.toRetirement? = some (aluRetirement s input op rd src1 src2)

theorem RvfiObservation.aluBoundary_fields
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (op : AluOp) (rd : Reg) (src1 : Src1) (src2 : Src2)
    (h : o.aluBoundary s input w op rd src1 src2) :
    o.aluFields s input w op rd src1 src2 := h.1

theorem RvfiObservation.aluBoundary_semantic
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (op : AluOp) (rd : Reg) (src1 : Src1) (src2 : Src2)
    (h : o.aluBoundary s input w op rd src1 src2) :
    o.toRetirement? = some (aluRetirement s input op rd src1 src2) := h.2

theorem RvfiObservation.aluBoundary_rvMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (op : AluOp) (rd : Reg)
    (src1 : Src1) (src2 : Src2)
    (h : o.aluBoundary s input w op rd src1 src2) :
    (rvMachineWith profile).step s input =
      (aluNext s op rd src1 src2,
        aluRetirement s input op rd src1 src2) := by
  have hirq := h.1.1
  have hfetched := h.1.2.1
  have hdecode := h.1.2.2.1
  have hinput : input =
      { fetched := .word w, memory := input.memory, irq := 0 } := by
    cases input with
    | mk fetched memory irq =>
        simp_all
  rw [hinput]
  exact rvMachineWith_alu profile s input.memory w op rd src1 src2 hdecode

theorem RvfiObservation.aluBoundary_rvMemoryMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (op : AluOp) (rd : Reg)
    (src1 : Src1) (src2 : Src2)
    (h : o.aluBoundary s input w op rd src1 src2) :
    (rvMemoryMachineWith profile).step
        { arch := s, memory := input.memory } input =
      ({ arch := aluNext s op rd src1 src2, memory := input.memory },
        aluRetirement s input op rd src1 src2) := by
  have hirq := h.1.1
  have hfetched := h.1.2.1
  have hdecode := h.1.2.2.1
  have hinput : input =
      { fetched := .word w, memory := input.memory, irq := 0 } := by
    cases input with
    | mk fetched memory irq =>
        simp_all
  rw [hinput]
  simp only [rvMemoryMachineWith]
  rw [isaStepWith_alu profile s input.memory w op rd src1 src2 hdecode]
  rfl

/-! ## Core-facing ALU cycle case -/

theorem rvfiCycleStepRefines_of_alu_memory
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hinit : rel machine.init (rvMemoryMachineWith profile).init)
    (hstep : ∀ (state : State) (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ w op rd src1 src2,
          input.memory = memoryState.memory ∧
          observation.aluBoundary memoryState.arch input w op rd src1 src2 ∧
          rel state'
            { arch := aluNext memoryState.arch op rd src1 src2,
              memory := memoryState.memory }
      else rel state' memoryState) :
    RvfiCycleStepRefines machine (rvMemoryMachineWith profile) rel admit := by
  refine rvfiCycleStepRefines_of_memory_step profile machine rel admit hinit ?_
  intro state memoryState input hrel hadmit
  have hcase := hstep state memoryState input hrel hadmit
  rcases hmachine : machine.step state input with ⟨state', observation⟩
  simp only [hmachine] at hcase ⊢
  by_cases hv : observation.valid = true
  · have hcase' : ∃ w op rd src1 src2,
        input.memory = memoryState.memory ∧
        observation.aluBoundary memoryState.arch input w op rd src1 src2 ∧
        rel state'
          { arch := aluNext memoryState.arch op rd src1 src2,
            memory := memoryState.memory } := by
      simpa [hv] using hcase
    rcases hcase' with ⟨w, op, rd, src1, src2, hmem, hboundary, hrel'⟩
    have hwell : observation.wellFormed := by
      exact hboundary.1.2.2.2.2.1
    have hto : observation.toRetirement =
        aluRetirement memoryState.arch input op rd src1 src2 := by
      have hsome := observation.toRetirement?_eq_some hv hwell
      exact Option.some.inj (hsome.symm.trans hboundary.2)
    have hstate : memoryState =
        { arch := memoryState.arch, memory := input.memory } := by
      cases memoryState with
      | mk arch memory => simp [hmem]
    have hstepAlu := observation.aluBoundary_rvMemoryMachineWith
      profile memoryState.arch input w op rd src1 src2 hboundary
    have hstepAlu' :
        (rvMemoryMachineWith profile).step memoryState input =
          ({ arch := aluNext memoryState.arch op rd src1 src2,
             memory := memoryState.memory },
            aluRetirement memoryState.arch input op rd src1 src2) := by
      rw [hstate]
      simpa [hmem] using hstepAlu
    simp only [hv]
    exact ⟨_, aluRetirement memoryState.arch input op rd src1 src2,
      hmem, hwell, hto, hstepAlu', hrel'⟩
  · have hv' : observation.valid = false := by
      cases hvalue : observation.valid with
      | false => exact rfl
      | true => exact False.elim (hv hvalue)
    have hrel' : rel state' memoryState := by
      simpa [hv, hv'] using hcase
    simp only [hv]
    exact hrel'

#print axioms LeanModels.Refine.RvfiObservation.aluBoundary
#print axioms LeanModels.Refine.RvfiObservation.aluBoundary_rvMachineWith
#print axioms LeanModels.Refine.RvfiObservation.aluBoundary_rvMemoryMachineWith
#print axioms LeanModels.Refine.rvfiCycleStepRefines_of_alu_memory

end LeanModels.Refine
