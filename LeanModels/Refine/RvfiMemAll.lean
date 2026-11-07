import LeanModels.Refine.RvfiMem
import LeanModels.Refine.Rv32iMemAll

/-!
# Raw RVFI boundary for all RV32I memory forms

The generic predicate covers loads and stores at byte, halfword, and word
widths.  A load keeps its signedness in the returned value; a store keeps its
source register and the exact byte mask.  The threaded cycle constructor then
shares one state relation for all six byte/halfword variants and both existing
word variants.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-- The common raw RVFI facts for a memory operation. -/
def RvfiObservation.memFields (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (kind : MemOp)
    (r rs1 : Reg) (imm : Word) : Prop :=
  input.irq = 0 ∧
  input.fetched = .word w ∧
  Fetched.decode (.word w) = some (kind.toInstr r rs1 imm) ∧
  o.valid = true ∧
  o.wellFormed ∧
  o.insn = w ∧
  o.pcRdata = s.pc ∧
  o.pcWdata = s.pc + 4 ∧
  match kind with
  | .load signed width =>
      o.rs1Addr = rs1 ∧
      o.rs1Rdata = s.readReg rs1 ∧
      o.rdAddr = r ∧
      o.rdWdata = loadVal input.memory width signed (s.readReg rs1 + imm) ∧
      o.memAddr = s.readReg rs1 + imm ∧
      o.memRmask = maskOfWidth width ∧
      o.memWmask = 0 ∧
      o.memRdata = loadVal input.memory width signed (s.readReg rs1 + imm) ∧
      o.trap = false ∧
      o.intr = false ∧
      o.cause = none
  | .store width =>
      o.rs1Addr = rs1 ∧
      o.rs1Rdata = s.readReg rs1 ∧
      o.rs2Addr = r ∧
      o.rs2Rdata = s.readReg r ∧
      o.rdWdataValid = false ∧
      o.memAddr = s.readReg rs1 + imm ∧
      o.memRmask = 0 ∧
      o.memWmask = maskOfWidth width ∧
      o.memWdata = s.readReg r ∧
      o.trap = false ∧
      o.intr = false ∧
      o.cause = none

def RvfiObservation.memBoundary (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (kind : MemOp)
    (r rs1 : Reg) (imm : Word) : Prop :=
  o.memFields s input w kind r rs1 imm ∧
  o.toRetirement? = some (memRetirement s input kind r rs1 imm)

theorem RvfiObservation.memBoundary_fields
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (kind : MemOp) (r rs1 : Reg) (imm : Word)
    (h : o.memBoundary s input w kind r rs1 imm) :
    o.memFields s input w kind r rs1 imm := h.1

theorem RvfiObservation.memBoundary_semantic
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (kind : MemOp) (r rs1 : Reg) (imm : Word)
    (h : o.memBoundary s input w kind r rs1 imm) :
    o.toRetirement? = some (memRetirement s input kind r rs1 imm) := h.2

theorem RvfiObservation.memBoundary_rvMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (kind : MemOp) (r rs1 : Reg) (imm : Word)
    (h : o.memBoundary s input w kind r rs1 imm) :
    (rvMachineWith profile).step s input =
      (memNext s input.memory kind r rs1 imm,
        memRetirement s input kind r rs1 imm) := by
  have hirq := h.1.1
  have hfetched := h.1.2.1
  have hdecode := h.1.2.2.1
  have hinput : input =
      { fetched := .word w, memory := input.memory, irq := 0 } := by
    cases input with
    | mk fetched memory irq =>
        simp_all
  rw [hinput]
  exact rvMachineWith_mem profile s input.memory w kind r rs1 imm hdecode

theorem RvfiObservation.memBoundary_rvMemoryMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (kind : MemOp) (r rs1 : Reg) (imm : Word)
    (h : o.memBoundary s input w kind r rs1 imm) :
    (rvMemoryMachineWith profile).step
        { arch := s, memory := input.memory } input =
      ({ arch := memNext s input.memory kind r rs1 imm,
         memory := memAfter input.memory s kind r rs1 imm },
        memRetirement s input kind r rs1 imm) := by
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
  rw [isaStepWith_mem profile s input.memory w kind r rs1 imm hdecode]
  cases kind <;> rfl

/-! ## Core-facing generic memory cycle case -/

theorem rvfiCycleStepRefines_of_mem_memory
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hinit : rel machine.init (rvMemoryMachineWith profile).init)
    (hstep : ∀ (state : State) (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ w kind r rs1 imm,
          input.memory = memoryState.memory ∧
          observation.memBoundary memoryState.arch input w kind r rs1 imm ∧
          rel state'
            { arch := memNext memoryState.arch memoryState.memory kind r rs1 imm,
              memory := memAfter memoryState.memory memoryState.arch kind r rs1 imm }
      else rel state' memoryState) :
    RvfiCycleStepRefines machine (rvMemoryMachineWith profile) rel admit := by
  refine rvfiCycleStepRefines_of_memory_step profile machine rel admit hinit ?_
  intro state memoryState input hrel hadmit
  have hcase := hstep state memoryState input hrel hadmit
  rcases hmachine : machine.step state input with ⟨state', observation⟩
  simp only [hmachine] at hcase ⊢
  by_cases hv : observation.valid = true
  · have hcase' : ∃ w kind r rs1 imm,
        input.memory = memoryState.memory ∧
        observation.memBoundary memoryState.arch input w kind r rs1 imm ∧
        rel state'
          { arch := memNext memoryState.arch memoryState.memory kind r rs1 imm,
            memory := memAfter memoryState.memory memoryState.arch kind r rs1 imm } := by
      simpa [hv] using hcase
    rcases hcase' with ⟨w, kind, r, rs1, imm, hmem, hboundary, hrel'⟩
    have hwell : observation.wellFormed := by
      exact hboundary.1.2.2.2.2.1
    have hto : observation.toRetirement =
        memRetirement memoryState.arch input kind r rs1 imm := by
      have hsome := observation.toRetirement?_eq_some hv hwell
      exact Option.some.inj (hsome.symm.trans hboundary.2)
    have hstate : memoryState =
        { arch := memoryState.arch, memory := input.memory } := by
      cases memoryState with
      | mk arch memory => simp [hmem]
    have hstepMem := observation.memBoundary_rvMemoryMachineWith
      profile memoryState.arch input w kind r rs1 imm hboundary
    have hstepMem' :
        (rvMemoryMachineWith profile).step memoryState input =
          ({ arch := memNext memoryState.arch memoryState.memory kind r rs1 imm,
             memory := memAfter memoryState.memory memoryState.arch kind r rs1 imm },
            memRetirement memoryState.arch input kind r rs1 imm) := by
      rw [hstate]
      simpa [hmem] using hstepMem
    simp only [hv]
    exact ⟨_, memRetirement memoryState.arch input kind r rs1 imm,
      hmem, hwell, hto, hstepMem', hrel'⟩
  · have hv' : observation.valid = false := by
      cases hvalue : observation.valid with
      | false => exact rfl
      | true => exact False.elim (hv hvalue)
    have hrel' : rel state' memoryState := by
      simpa [hv, hv'] using hcase
    simp only [hv]
    exact hrel'

#print axioms LeanModels.Refine.RvfiObservation.memBoundary
#print axioms LeanModels.Refine.RvfiObservation.memBoundary_rvMachineWith
#print axioms LeanModels.Refine.RvfiObservation.memBoundary_rvMemoryMachineWith
#print axioms LeanModels.Refine.rvfiCycleStepRefines_of_mem_memory

end LeanModels.Refine
