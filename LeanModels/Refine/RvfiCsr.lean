import LeanModels.Refine.RvfiSystem
import LeanModels.Refine.Rv32iCsr

/-!
# Raw RVFI Zicsr boundary

The CSR row is retained at the raw boundary: a valid observation must decode to
the selected operation and address an implemented `CsrBehavior` row.  The
register readback, pc advance, and absence of data-memory/trap effects are
checked in the packed fields; the stateful cycle theorem carries the WARL CSR
file update through `csrNext`.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## Raw CSR predicate -/

/-- The source-register portion of a CSR observation.  Immediate forms have
no architectural `rs1` read, so their packed source fields remain
unconstrained just as immediate ALU sources do. -/
def csrSrcFields (s : ArchState) (o : RvfiObservation) : CsrSrc → Prop
  | .reg r => o.rs1Addr = r ∧ o.rs1Rdata = s.readReg r
  | .imm _ => True

/-- The raw RVFI facts for one implemented 32-bit Zicsr operation. -/
def RvfiObservation.csrFields (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (row : CsrBehavior)
    (kind : CsrOpKind) : Prop :=
  input.irq = 0 ∧
  input.fetched = .word w ∧
  Fetched.decode (.word w) = some kind.toInstr ∧
  findCsr? kind.addr = some row ∧
  o.valid = true ∧
  o.wellFormed ∧
  o.insn = w ∧
  o.pcRdata = s.pc ∧
  o.pcWdata = s.pc + 4 ∧
  csrSrcFields s o kind.src ∧
  o.rdAddr = kind.rd ∧
  o.rdWdata = csrOld s row ∧
  o.rdWdataValid = true ∧
  o.trap = false ∧
  o.intr = false ∧
  o.memRmask = 0 ∧
  o.memWmask = 0 ∧
  o.cause = none

def RvfiObservation.csrBoundary (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (row : CsrBehavior)
    (kind : CsrOpKind) : Prop :=
  o.csrFields s input w row kind ∧
  o.toRetirement? = some (csrRetirement s input row kind)

theorem RvfiObservation.csrBoundary_fields
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (row : CsrBehavior) (kind : CsrOpKind)
    (h : o.csrBoundary s input w row kind) :
    o.csrFields s input w row kind := h.1

theorem RvfiObservation.csrBoundary_semantic
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (row : CsrBehavior) (kind : CsrOpKind)
    (h : o.csrBoundary s input w row kind) :
    o.toRetirement? = some (csrRetirement s input row kind) := h.2

theorem RvfiObservation.csrBoundary_rvMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (row : CsrBehavior) (kind : CsrOpKind)
    (h : o.csrBoundary s input w row kind) :
    (rvMachineWith profile).step s input =
      (csrNext s row kind, csrRetirement s input row kind) := by
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
  exact rvMachineWith_csr profile s input.memory w row kind hdecode hrow

theorem RvfiObservation.csrBoundary_rvMemoryMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (row : CsrBehavior) (kind : CsrOpKind)
    (h : o.csrBoundary s input w row kind) :
    (rvMemoryMachineWith profile).step
        { arch := s, memory := input.memory } input =
      ({ arch := csrNext s row kind, memory := input.memory },
        csrRetirement s input row kind) := by
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
  rw [isaStepWith_csr profile s input.memory w row kind hdecode hrow]
  rfl

/-! ## Core-facing CSR cycle case -/

theorem rvfiCycleStepRefines_of_csr_memory
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hinit : rel machine.init (rvMemoryMachineWith profile).init)
    (hstep : ∀ (state : State) (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ w row kind,
          input.memory = memoryState.memory ∧
          observation.csrBoundary memoryState.arch input w row kind ∧
          rel state'
            { arch := csrNext memoryState.arch row kind,
              memory := memoryState.memory }
      else rel state' memoryState) :
    RvfiCycleStepRefines machine (rvMemoryMachineWith profile) rel admit := by
  refine rvfiCycleStepRefines_of_memory_step profile machine rel admit hinit ?_
  intro state memoryState input hrel hadmit
  have hcase := hstep state memoryState input hrel hadmit
  rcases hmachine : machine.step state input with ⟨state', observation⟩
  simp only [hmachine] at hcase ⊢
  by_cases hv : observation.valid = true
  · have hcase' : ∃ w row kind,
        input.memory = memoryState.memory ∧
        observation.csrBoundary memoryState.arch input w row kind ∧
        rel state'
          { arch := csrNext memoryState.arch row kind,
            memory := memoryState.memory } := by
      simpa [hv] using hcase
    rcases hcase' with ⟨w, row, kind, hmem, hboundary, hrel'⟩
    have hwell : observation.wellFormed := by
      exact hboundary.1.2.2.2.2.2.1
    have hto : observation.toRetirement =
        csrRetirement memoryState.arch input row kind := by
      have hsome := observation.toRetirement?_eq_some hv hwell
      exact Option.some.inj (hsome.symm.trans hboundary.2)
    have hstate : memoryState =
        { arch := memoryState.arch, memory := input.memory } := by
      cases memoryState with
      | mk arch memory => simp [hmem]
    have hstepCsr := observation.csrBoundary_rvMemoryMachineWith
      profile memoryState.arch input w row kind hboundary
    have hstepCsr' :
        (rvMemoryMachineWith profile).step memoryState input =
          ({ arch := csrNext memoryState.arch row kind,
             memory := memoryState.memory },
            csrRetirement memoryState.arch input row kind) := by
      rw [hstate]
      simpa [hmem] using hstepCsr
    simp only [hv]
    exact ⟨_, csrRetirement memoryState.arch input row kind,
      hmem, hwell, hto, hstepCsr', hrel'⟩
  · have hv' : observation.valid = false := by
      cases hvalue : observation.valid with
      | false => exact rfl
      | true => exact False.elim (hv hvalue)
    have hrel' : rel state' memoryState := by
      simpa [hv, hv'] using hcase
    simp only [hv]
    exact hrel'

#print axioms LeanModels.Refine.RvfiObservation.csrBoundary
#print axioms LeanModels.Refine.RvfiObservation.csrBoundary_rvMachineWith
#print axioms LeanModels.Refine.RvfiObservation.csrBoundary_rvMemoryMachineWith
#print axioms LeanModels.Refine.rvfiCycleStepRefines_of_csr_memory

end LeanModels.Refine
