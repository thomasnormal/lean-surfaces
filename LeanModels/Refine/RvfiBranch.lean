import LeanModels.Refine.RvfiMem
import LeanModels.Refine.Rv32iBranch

/-!
# Raw RVFI conditional-branch boundary

All six RV32I conditional branches have the same wire shape.  The condition is
kept as a parameter, while the raw predicate records both source reads and the
chosen pc target.  There is no register write or data-memory effect; the
stateful cycle constructor therefore only changes the architectural pc and
preserves the threaded memory.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-- The raw RVFI facts for a 32-bit conditional branch. -/
def RvfiObservation.branchFields (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (cond : BranchCond)
    (rs1 rs2 : Reg) (offset : Word) : Prop :=
  input.irq = 0 ∧
  input.fetched = .word w ∧
  Fetched.decode (.word w) = some (.branch cond rs1 rs2 offset) ∧
  o.valid = true ∧
  o.wellFormed ∧
  o.insn = w ∧
  o.pcRdata = s.pc ∧
  o.pcWdata = branchTarget s cond rs1 rs2 offset ∧
  o.rs1Addr = rs1 ∧
  o.rs1Rdata = s.readReg rs1 ∧
  o.rs2Addr = rs2 ∧
  o.rs2Rdata = s.readReg rs2 ∧
  o.rdWdataValid = false ∧
  o.memRmask = 0 ∧
  o.memWmask = 0 ∧
  o.trap = false ∧
  o.intr = false ∧
  o.cause = none

def RvfiObservation.branchBoundary (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (cond : BranchCond)
    (rs1 rs2 : Reg) (offset : Word) : Prop :=
  o.branchFields s input w cond rs1 rs2 offset ∧
  o.toRetirement? = some (branchRetirement s input cond rs1 rs2 offset)

theorem RvfiObservation.branchBoundary_fields
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (cond : BranchCond) (rs1 rs2 : Reg) (offset : Word)
    (h : o.branchBoundary s input w cond rs1 rs2 offset) :
    o.branchFields s input w cond rs1 rs2 offset := h.1

theorem RvfiObservation.branchBoundary_semantic
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (cond : BranchCond) (rs1 rs2 : Reg) (offset : Word)
    (h : o.branchBoundary s input w cond rs1 rs2 offset) :
    o.toRetirement? = some (branchRetirement s input cond rs1 rs2 offset) := h.2

theorem RvfiObservation.branchBoundary_rvMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (cond : BranchCond) (rs1 rs2 : Reg)
    (offset : Word) (h : o.branchBoundary s input w cond rs1 rs2 offset) :
    (rvMachineWith profile).step s input =
      (branchNext s cond rs1 rs2 offset,
        branchRetirement s input cond rs1 rs2 offset) := by
  have hirq := h.1.1
  have hfetched := h.1.2.1
  have hdecode := h.1.2.2.1
  have hinput : input =
      { fetched := .word w, memory := input.memory, irq := 0 } := by
    cases input with
    | mk fetched memory irq =>
        simp_all
  rw [hinput]
  exact rvMachineWith_branch profile s input.memory w cond rs1 rs2 offset hdecode

theorem RvfiObservation.branchBoundary_rvMemoryMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (cond : BranchCond) (rs1 rs2 : Reg)
    (offset : Word) (h : o.branchBoundary s input w cond rs1 rs2 offset) :
    (rvMemoryMachineWith profile).step
        { arch := s, memory := input.memory } input =
      ({ arch := branchNext s cond rs1 rs2 offset, memory := input.memory },
        branchRetirement s input cond rs1 rs2 offset) := by
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
  rw [isaStepWith_branch profile s input.memory w cond rs1 rs2 offset hdecode]
  rfl

/-! ## Core-facing branch cycle case -/

theorem rvfiCycleStepRefines_of_branch_memory
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hinit : rel machine.init (rvMemoryMachineWith profile).init)
    (hstep : ∀ (state : State) (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ w cond rs1 rs2 offset,
          input.memory = memoryState.memory ∧
          observation.branchBoundary memoryState.arch input w cond rs1 rs2 offset ∧
          rel state'
            { arch := branchNext memoryState.arch cond rs1 rs2 offset,
              memory := memoryState.memory }
      else rel state' memoryState) :
    RvfiCycleStepRefines machine (rvMemoryMachineWith profile) rel admit := by
  refine rvfiCycleStepRefines_of_memory_step profile machine rel admit hinit ?_
  intro state memoryState input hrel hadmit
  have hcase := hstep state memoryState input hrel hadmit
  rcases hmachine : machine.step state input with ⟨state', observation⟩
  simp only [hmachine] at hcase ⊢
  by_cases hv : observation.valid = true
  · have hcase' : ∃ w cond rs1 rs2 offset,
        input.memory = memoryState.memory ∧
        observation.branchBoundary memoryState.arch input w cond rs1 rs2 offset ∧
        rel state'
          { arch := branchNext memoryState.arch cond rs1 rs2 offset,
            memory := memoryState.memory } := by
      simpa [hv] using hcase
    rcases hcase' with ⟨w, cond, rs1, rs2, offset, hmem, hboundary, hrel'⟩
    have hwell : observation.wellFormed := by
      exact hboundary.1.2.2.2.2.1
    have hto : observation.toRetirement =
        branchRetirement memoryState.arch input cond rs1 rs2 offset := by
      have hsome := observation.toRetirement?_eq_some hv hwell
      exact Option.some.inj (hsome.symm.trans hboundary.2)
    have hstate : memoryState =
        { arch := memoryState.arch, memory := input.memory } := by
      cases memoryState with
      | mk arch memory => simp [hmem]
    have hstepBranch := observation.branchBoundary_rvMemoryMachineWith
      profile memoryState.arch input w cond rs1 rs2 offset hboundary
    have hstepBranch' :
        (rvMemoryMachineWith profile).step memoryState input =
          ({ arch := branchNext memoryState.arch cond rs1 rs2 offset,
             memory := memoryState.memory },
            branchRetirement memoryState.arch input cond rs1 rs2 offset) := by
      rw [hstate]
      simpa [hmem] using hstepBranch
    simp only [hv]
    exact ⟨_, branchRetirement memoryState.arch input cond rs1 rs2 offset,
      hmem, hwell, hto, hstepBranch', hrel'⟩
  · have hv' : observation.valid = false := by
      cases hvalue : observation.valid with
      | false => exact rfl
      | true => exact False.elim (hv hvalue)
    have hrel' : rel state' memoryState := by
      simpa [hv, hv'] using hcase
    simp only [hv]
    exact hrel'

#print axioms LeanModels.Refine.RvfiObservation.branchBoundary
#print axioms LeanModels.Refine.RvfiObservation.branchBoundary_rvMachineWith
#print axioms LeanModels.Refine.RvfiObservation.branchBoundary_rvMemoryMachineWith
#print axioms LeanModels.Refine.rvfiCycleStepRefines_of_branch_memory

end LeanModels.Refine
