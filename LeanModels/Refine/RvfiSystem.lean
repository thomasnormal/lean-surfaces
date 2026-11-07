import LeanModels.Refine.RvfiMemAll
import LeanModels.Refine.Rv32iSystem

/-!
# Raw RVFI system-transfer boundaries

The raw predicate keeps the trap cause and handler pc for ECALL/EBREAK,
the MRET target, and the no-wake WFI stutter visible at the wire boundary.
Its semantic half is the shared system retirement, so a core invariant cannot
turn a malformed system row into a no-op.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-- The raw RVFI facts for one admitted non-CSR system operation. -/
def RvfiObservation.systemFields (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (kind : SysKind) : Prop :=
  input.irq = 0 ∧
  input.fetched = .word w ∧
  Fetched.decode (.word w) = some (.system kind.toSysOp) ∧
  o.valid = true ∧
  o.wellFormed ∧
  o.insn = w ∧
  o.pcRdata = s.pc ∧
  match kind with
  | .ecall =>
      o.pcWdata = (trapEnter s .ecallM).pc ∧
      o.rdWdataValid = false ∧
      o.trap = true ∧
      o.intr = false ∧
      o.memRmask = 0 ∧
      o.memWmask = 0 ∧
      o.cause = some .ecallM
  | .ebreak =>
      o.pcWdata = (trapEnter s .breakpoint).pc ∧
      o.rdWdataValid = false ∧
      o.trap = true ∧
      o.intr = false ∧
      o.memRmask = 0 ∧
      o.memWmask = 0 ∧
      o.cause = some .breakpoint
  | .mret =>
      o.pcWdata = (mret s).pc ∧
      o.rdWdataValid = false ∧
      o.trap = false ∧
      o.intr = false ∧
      o.memRmask = 0 ∧
      o.memWmask = 0 ∧
      o.cause = none
  | .wfi =>
      o.pcWdata = s.pc ∧
      o.rdWdataValid = false ∧
      o.trap = false ∧
      o.intr = false ∧
      o.memRmask = 0 ∧
      o.memWmask = 0 ∧
      o.cause = none

def RvfiObservation.systemBoundary (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (kind : SysKind) : Prop :=
  o.systemFields s input w kind ∧
  o.toRetirement? = some (systemRetirement s input kind)

theorem RvfiObservation.systemBoundary_fields
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (kind : SysKind)
    (h : o.systemBoundary s input w kind) :
    o.systemFields s input w kind := h.1

theorem RvfiObservation.systemBoundary_semantic
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (kind : SysKind)
    (h : o.systemBoundary s input w kind) :
    o.toRetirement? = some (systemRetirement s input kind) := h.2

theorem RvfiObservation.systemBoundary_rvMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (kind : SysKind)
    (h : o.systemBoundary s input w kind) :
    (rvMachineWith profile).step s input =
      (systemNext s kind, systemRetirement s input kind) := by
  have hirq := h.1.1
  have hfetched := h.1.2.1
  have hdecode := h.1.2.2.1
  have hinput : input =
      { fetched := .word w, memory := input.memory, irq := 0 } := by
    cases input with
    | mk fetched memory irq =>
        simp_all
  rw [hinput]
  exact rvMachineWith_system profile s input.memory w kind hdecode

theorem RvfiObservation.systemBoundary_rvMemoryMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (kind : SysKind)
    (h : o.systemBoundary s input w kind) :
    (rvMemoryMachineWith profile).step
        { arch := s, memory := input.memory } input =
      ({ arch := systemNext s kind, memory := input.memory },
        systemRetirement s input kind) := by
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
  rw [isaStepWith_system profile s input.memory w kind hdecode]
  cases kind <;> rfl

/-! ## Core-facing system cycle case -/

theorem rvfiCycleStepRefines_of_system_memory
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
          observation.systemBoundary memoryState.arch input w kind ∧
          rel state'
            { arch := systemNext memoryState.arch kind,
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
        observation.systemBoundary memoryState.arch input w kind ∧
        rel state'
          { arch := systemNext memoryState.arch kind,
            memory := memoryState.memory } := by
      simpa [hv] using hcase
    rcases hcase' with ⟨w, kind, hmem, hboundary, hrel'⟩
    have hwell : observation.wellFormed := by
      exact hboundary.1.2.2.2.2.1
    have hto : observation.toRetirement =
        systemRetirement memoryState.arch input kind := by
      have hsome := observation.toRetirement?_eq_some hv hwell
      exact Option.some.inj (hsome.symm.trans hboundary.2)
    have hstate : memoryState =
        { arch := memoryState.arch, memory := input.memory } := by
      cases memoryState with
      | mk arch memory => simp [hmem]
    have hstepSystem := observation.systemBoundary_rvMemoryMachineWith
      profile memoryState.arch input w kind hboundary
    have hstepSystem' :
        (rvMemoryMachineWith profile).step memoryState input =
          ({ arch := systemNext memoryState.arch kind,
             memory := memoryState.memory },
            systemRetirement memoryState.arch input kind) := by
      rw [hstate]
      simpa [hmem] using hstepSystem
    simp only [hv]
    exact ⟨_, systemRetirement memoryState.arch input kind, hmem, hwell,
      hto, hstepSystem', hrel'⟩
  · have hv' : observation.valid = false := by
      cases hvalue : observation.valid with
      | false => exact rfl
      | true => exact False.elim (hv hvalue)
    have hrel' : rel state' memoryState := by
      simpa [hv, hv'] using hcase
    simp only [hv]
    exact hrel'

#print axioms LeanModels.Refine.RvfiObservation.systemBoundary
#print axioms LeanModels.Refine.RvfiObservation.systemBoundary_rvMachineWith
#print axioms LeanModels.Refine.RvfiObservation.systemBoundary_rvMemoryMachineWith
#print axioms LeanModels.Refine.rvfiCycleStepRefines_of_system_memory

end LeanModels.Refine
