import LeanModels.Refine.RvfiMem
import LeanModels.Refine.Rv32iFence

/-!
# Raw RVFI fence boundaries

`fence` and `fence.i` share one raw wire shape: a valid sequential commit with
no register or data-memory effect.  `FenceKind` remains in the predicate so
the decoded system operation cannot be erased at the core-facing boundary.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-- The raw RVFI facts for a 32-bit fence operation. -/
def RvfiObservation.fenceFields (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (kind : FenceKind) : Prop :=
  input.irq = 0 ∧
  input.fetched = .word w ∧
  Fetched.decode (.word w) = some (.system kind.toSysOp) ∧
  o.valid = true ∧
  o.wellFormed ∧
  o.insn = w ∧
  o.pcRdata = s.pc ∧
  o.pcWdata = s.pc + 4 ∧
  o.rdWdataValid = false ∧
  o.trap = false ∧
  o.intr = false ∧
  o.memRmask = 0 ∧
  o.memWmask = 0 ∧
  o.cause = none

def RvfiObservation.fenceBoundary (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (kind : FenceKind) : Prop :=
  o.fenceFields s input w kind ∧
  o.toRetirement? = some (fenceRetirement s input kind)

theorem RvfiObservation.fenceBoundary_fields
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (kind : FenceKind)
    (h : o.fenceBoundary s input w kind) :
    o.fenceFields s input w kind := h.1

theorem RvfiObservation.fenceBoundary_semantic
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (kind : FenceKind)
    (h : o.fenceBoundary s input w kind) :
    o.toRetirement? = some (fenceRetirement s input kind) := h.2

theorem RvfiObservation.fenceBoundary_rvMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (kind : FenceKind)
    (h : o.fenceBoundary s input w kind) :
    (rvMachineWith profile).step s input =
      (fenceNext s kind, fenceRetirement s input kind) := by
  have hirq := h.1.1
  have hfetched := h.1.2.1
  have hdecode := h.1.2.2.1
  have hinput : input =
      { fetched := .word w, memory := input.memory, irq := 0 } := by
    cases input with
    | mk fetched memory irq =>
        simp_all
  rw [hinput]
  exact rvMachineWith_fence profile s input.memory w kind hdecode

theorem RvfiObservation.fenceBoundary_rvMemoryMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (kind : FenceKind)
    (h : o.fenceBoundary s input w kind) :
    (rvMemoryMachineWith profile).step
        { arch := s, memory := input.memory } input =
      ({ arch := fenceNext s kind, memory := input.memory },
        fenceRetirement s input kind) := by
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
  rw [isaStepWith_fence profile s input.memory w kind hdecode]
  rfl

/-! ## Core-facing fence cycle case -/

theorem rvfiCycleStepRefines_of_fence_memory
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hinit : rel machine.init (rvMemoryMachineWith profile).init)
    (hstep : ∀ (state : State) (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ w kind,
          input.memory = memoryState.memory ∧
          observation.fenceBoundary memoryState.arch input w kind ∧
          rel state'
            { arch := fenceNext memoryState.arch kind,
              memory := memoryState.memory }
      else rel state' memoryState) :
    RvfiCycleStepRefines machine (rvMemoryMachineWith profile) rel admit := by
  refine rvfiCycleStepRefines_of_memory_step profile machine rel admit hinit ?_
  intro state memoryState input hrel hadmit
  have hcase := hstep state memoryState input hrel hadmit
  rcases hmachine : machine.step state input with ⟨state', observation⟩
  simp only [hmachine] at hcase ⊢
  by_cases hv : observation.valid = true
  · have hcase' : ∃ w kind,
        input.memory = memoryState.memory ∧
        observation.fenceBoundary memoryState.arch input w kind ∧
        rel state'
          { arch := fenceNext memoryState.arch kind,
            memory := memoryState.memory } := by
      simpa [hv] using hcase
    rcases hcase' with ⟨w, kind, hmem, hboundary, hrel'⟩
    have hwell : observation.wellFormed := by
      exact hboundary.1.2.2.2.2.1
    have hto : observation.toRetirement =
        fenceRetirement memoryState.arch input kind := by
      have hsome := observation.toRetirement?_eq_some hv hwell
      exact Option.some.inj (hsome.symm.trans hboundary.2)
    have hstate : memoryState =
        { arch := memoryState.arch, memory := input.memory } := by
      cases memoryState with
      | mk arch memory => simp [hmem]
    have hstepFence := observation.fenceBoundary_rvMemoryMachineWith
      profile memoryState.arch input w kind hboundary
    have hstepFence' :
        (rvMemoryMachineWith profile).step memoryState input =
          ({ arch := fenceNext memoryState.arch kind,
             memory := memoryState.memory },
            fenceRetirement memoryState.arch input kind) := by
      rw [hstate]
      simpa [hmem] using hstepFence
    simp only [hv]
    exact ⟨_, fenceRetirement memoryState.arch input kind, hmem, hwell,
      hto, hstepFence', hrel'⟩
  · have hv' : observation.valid = false := by
      cases hvalue : observation.valid with
      | false => exact rfl
      | true => exact False.elim (hv hvalue)
    have hrel' : rel state' memoryState := by
      simpa [hv, hv'] using hcase
    simp only [hv]
    exact hrel'

#print axioms LeanModels.Refine.RvfiObservation.fenceBoundary
#print axioms LeanModels.Refine.RvfiObservation.fenceBoundary_rvMachineWith
#print axioms LeanModels.Refine.RvfiObservation.fenceBoundary_rvMemoryMachineWith
#print axioms LeanModels.Refine.rvfiCycleStepRefines_of_fence_memory

end LeanModels.Refine
