import LeanModels.Refine.RvfiCsr
import LeanModels.Refine.Rv32iTrap

/-!
# Raw RVFI illegal-instruction boundary

The raw predicate admits only an undecodable 32-bit parcel.  It retains the
precise illegal-instruction cause and trap handler pc, and requires clear
register/data-memory effects.  An unimplemented CSR has a separate boundary:
its word decodes as a CSR operation but the row lookup fails, so it cannot be
silently classified as an undecodable word.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## Decode-failure trap -/

/-- The raw RVFI facts for an undecodable 32-bit parcel. -/
def RvfiObservation.illegalFields (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) : Prop :=
  input.irq = 0 ∧
  input.fetched = .word w ∧
  Fetched.decode (.word w) = none ∧
  o.valid = true ∧
  o.wellFormed ∧
  o.insn = w ∧
  o.pcRdata = s.pc ∧
  o.pcWdata = (illegalNext s).pc ∧
  o.rdWdataValid = false ∧
  o.trap = true ∧
  o.intr = false ∧
  o.memRmask = 0 ∧
  o.memWmask = 0 ∧
  o.cause = some .illegalInstr

def RvfiObservation.illegalBoundary (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) : Prop :=
  o.illegalFields s input w ∧
  o.toRetirement? = some (illegalRetirement s input)

theorem RvfiObservation.illegalBoundary_fields
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (h : o.illegalBoundary s input w) :
    o.illegalFields s input w := h.1

theorem RvfiObservation.illegalBoundary_semantic
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (h : o.illegalBoundary s input w) :
    o.toRetirement? = some (illegalRetirement s input) := h.2

theorem RvfiObservation.illegalBoundary_rvMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word)
    (h : o.illegalBoundary s input w) :
    (rvMachineWith profile).step s input =
      (illegalNext s, illegalRetirement s input) := by
  have hirq := h.1.1
  have hfetched := h.1.2.1
  have hdecode := h.1.2.2.1
  have hinput : input =
      { fetched := .word w, memory := input.memory, irq := 0 } := by
    cases input with
    | mk fetched memory irq =>
        simp_all
  rw [hinput]
  exact rvMachineWith_illegal profile s input.memory w hdecode

theorem RvfiObservation.illegalBoundary_rvMemoryMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word)
    (h : o.illegalBoundary s input w) :
    (rvMemoryMachineWith profile).step
        { arch := s, memory := input.memory } input =
      ({ arch := illegalNext s, memory := input.memory },
        illegalRetirement s input) := by
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
  rw [isaStepWith_illegal profile s input.memory w hdecode]
  rfl

/-! ## Core-facing decode-failure cycle case -/

theorem rvfiCycleStepRefines_of_illegal_memory
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hinit : rel machine.init (rvMemoryMachineWith profile).init)
    (hstep : ∀ (state : State) (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ w,
          input.memory = memoryState.memory ∧
          observation.illegalBoundary memoryState.arch input w ∧
          rel state'
            { arch := illegalNext memoryState.arch,
              memory := memoryState.memory }
      else rel state' memoryState) :
    RvfiCycleStepRefines machine (rvMemoryMachineWith profile) rel admit := by
  refine rvfiCycleStepRefines_of_memory_step profile machine rel admit hinit ?_
  intro state memoryState input hrel hadmit
  have hcase := hstep state memoryState input hrel hadmit
  rcases hmachine : machine.step state input with ⟨state', observation⟩
  simp only [hmachine] at hcase ⊢
  by_cases hv : observation.valid = true
  · have hcase' : ∃ w,
        input.memory = memoryState.memory ∧
        observation.illegalBoundary memoryState.arch input w ∧
        rel state'
          { arch := illegalNext memoryState.arch,
            memory := memoryState.memory } := by
      simpa [hv] using hcase
    rcases hcase' with ⟨w, hmem, hboundary, hrel'⟩
    have hwell : observation.wellFormed := by
      exact hboundary.1.2.2.2.2.1
    have hto : observation.toRetirement =
        illegalRetirement memoryState.arch input := by
      have hsome := observation.toRetirement?_eq_some hv hwell
      exact Option.some.inj (hsome.symm.trans hboundary.2)
    have hstate : memoryState =
        { arch := memoryState.arch, memory := input.memory } := by
      cases memoryState with
      | mk arch memory => simp [hmem]
    have hstepIllegal := observation.illegalBoundary_rvMemoryMachineWith
      profile memoryState.arch input w hboundary
    have hstepIllegal' :
        (rvMemoryMachineWith profile).step memoryState input =
          ({ arch := illegalNext memoryState.arch,
             memory := memoryState.memory },
            illegalRetirement memoryState.arch input) := by
      rw [hstate]
      simpa [hmem] using hstepIllegal
    simp only [hv]
    exact ⟨_, illegalRetirement memoryState.arch input,
      hmem, hwell, hto, hstepIllegal', hrel'⟩
  · have hv' : observation.valid = false := by
      cases hvalue : observation.valid with
      | false => exact rfl
      | true => exact False.elim (hv hvalue)
    have hrel' : rel state' memoryState := by
      simpa [hv, hv'] using hcase
    simp only [hv]
    exact hrel'

/-! ## Unimplemented CSR trap -/

/-- The raw RVFI facts for a decoded Zicsr parcel whose address is absent from
the implemented CSR table.  Its source and destination payloads are left
unconstrained because the architectural step traps before reading or writing
the CSR operation. -/
def RvfiObservation.illegalCsrFields (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (kind : CsrOpKind) : Prop :=
  input.irq = 0 ∧
  input.fetched = .word w ∧
  Fetched.decode (.word w) = some kind.toInstr ∧
  findCsr? kind.addr = none ∧
  o.valid = true ∧
  o.wellFormed ∧
  o.insn = w ∧
  o.pcRdata = s.pc ∧
  o.pcWdata = (illegalNext s).pc ∧
  o.rdWdataValid = false ∧
  o.trap = true ∧
  o.intr = false ∧
  o.memRmask = 0 ∧
  o.memWmask = 0 ∧
  o.cause = some .illegalInstr

def RvfiObservation.illegalCsrBoundary (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (kind : CsrOpKind) : Prop :=
  o.illegalCsrFields s input w kind ∧
  o.toRetirement? = some (illegalRetirement s input)

theorem RvfiObservation.illegalCsrBoundary_fields
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (kind : CsrOpKind)
    (h : o.illegalCsrBoundary s input w kind) :
    o.illegalCsrFields s input w kind := h.1

theorem RvfiObservation.illegalCsrBoundary_semantic
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (kind : CsrOpKind)
    (h : o.illegalCsrBoundary s input w kind) :
    o.toRetirement? = some (illegalRetirement s input) := h.2

theorem RvfiObservation.illegalCsrBoundary_rvMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (kind : CsrOpKind)
    (h : o.illegalCsrBoundary s input w kind) :
    (rvMachineWith profile).step s input =
      (illegalNext s, illegalRetirement s input) := by
  have hirq := h.1.1
  have hfetched := h.1.2.1
  have hdecode := h.1.2.2.1
  have hrow := h.1.2.2.2.1
  have hinput : input =
      { fetched := .word w, memory := input.memory, irq := 0 } := by
    cases input with
    | mk fetched memory irq =>
        simp_all
  rw [hinput]
  exact rvMachineWith_illegal_csr profile s input.memory w kind hdecode hrow

theorem RvfiObservation.illegalCsrBoundary_rvMemoryMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (kind : CsrOpKind)
    (h : o.illegalCsrBoundary s input w kind) :
    (rvMemoryMachineWith profile).step
        { arch := s, memory := input.memory } input =
      ({ arch := illegalNext s, memory := input.memory },
        illegalRetirement s input) := by
  have hirq := h.1.1
  have hfetched := h.1.2.1
  have hdecode := h.1.2.2.1
  have hrow := h.1.2.2.2.1
  have hinput : input =
      { fetched := .word w, memory := input.memory, irq := 0 } := by
    cases input with
    | mk fetched memory irq =>
        simp_all
  rw [hinput]
  simp only [rvMemoryMachineWith]
  rw [isaStepWith_illegal_csr profile s input.memory w kind hdecode hrow]
  rfl

theorem rvfiCycleStepRefines_of_illegal_csr_memory
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
          observation.illegalCsrBoundary memoryState.arch input w kind ∧
          rel state'
            { arch := illegalNext memoryState.arch,
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
        observation.illegalCsrBoundary memoryState.arch input w kind ∧
        rel state'
          { arch := illegalNext memoryState.arch,
            memory := memoryState.memory } := by
      simpa [hv] using hcase
    rcases hcase' with ⟨w, kind, hmem, hboundary, hrel'⟩
    have hwell : observation.wellFormed := by
      exact hboundary.1.2.2.2.2.2.1
    have hto : observation.toRetirement =
        illegalRetirement memoryState.arch input := by
      have hsome := observation.toRetirement?_eq_some hv hwell
      exact Option.some.inj (hsome.symm.trans hboundary.2)
    have hstate : memoryState =
        { arch := memoryState.arch, memory := input.memory } := by
      cases memoryState with
      | mk arch memory => simp [hmem]
    have hstepIllegal := observation.illegalCsrBoundary_rvMemoryMachineWith
      profile memoryState.arch input w kind hboundary
    have hstepIllegal' :
        (rvMemoryMachineWith profile).step memoryState input =
          ({ arch := illegalNext memoryState.arch,
             memory := memoryState.memory },
            illegalRetirement memoryState.arch input) := by
      rw [hstate]
      simpa [hmem] using hstepIllegal
    simp only [hv]
    exact ⟨_, illegalRetirement memoryState.arch input,
      hmem, hwell, hto, hstepIllegal', hrel'⟩
  · have hv' : observation.valid = false := by
      cases hvalue : observation.valid with
      | false => exact rfl
      | true => exact False.elim (hv hvalue)
    have hrel' : rel state' memoryState := by
      simpa [hv, hv'] using hcase
    simp only [hv]
    exact hrel'

#print axioms LeanModels.Refine.RvfiObservation.illegalBoundary
#print axioms LeanModels.Refine.RvfiObservation.illegalBoundary_rvMachineWith
#print axioms LeanModels.Refine.RvfiObservation.illegalBoundary_rvMemoryMachineWith
#print axioms LeanModels.Refine.rvfiCycleStepRefines_of_illegal_memory
#print axioms LeanModels.Refine.RvfiObservation.illegalCsrBoundary
#print axioms LeanModels.Refine.RvfiObservation.illegalCsrBoundary_rvMachineWith
#print axioms LeanModels.Refine.RvfiObservation.illegalCsrBoundary_rvMemoryMachineWith
#print axioms LeanModels.Refine.rvfiCycleStepRefines_of_illegal_csr_memory

end LeanModels.Refine
