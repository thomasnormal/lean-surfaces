import LeanModels.Refine.RvfiMem
import LeanModels.Refine.Rv32iUpper

/-!
# Raw RVFI LUI boundary

The LUI row is represented by the existing ALU family with register x0 as its
first source.  The raw predicate keeps that source read explicit, together
with the decoded word and the no-memory/no-trap facts, before the generic
threaded-memory constructor consumes the row.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## Raw LUI predicate -/

def RvfiObservation.luiFields (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (rd : Reg) (imm : Word) : Prop :=
  input.irq = 0 ∧
  input.fetched = .word w ∧
  Fetched.decode (.word w) =
    some (.alu .add rd (.reg 0) (.imm imm)) ∧
  o.valid = true ∧
  o.wellFormed ∧
  o.insn = w ∧
  o.pcRdata = s.pc ∧
  o.pcWdata = s.pc + 4 ∧
  o.rs1Addr = 0 ∧
  o.rs1Rdata = s.readReg 0 ∧
  o.rdAddr = rd ∧
  o.rdWdata = s.readReg 0 + imm ∧
  o.trap = false ∧
  o.intr = false ∧
  o.memRmask = 0 ∧
  o.memWmask = 0 ∧
  o.cause = none

def RvfiObservation.luiBoundary (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (rd : Reg) (imm : Word) : Prop :=
  o.luiFields s input w rd imm ∧
  o.toRetirement? = some (luiRetirement s input rd imm)

theorem RvfiObservation.luiBoundary_fields
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (rd : Reg) (imm : Word)
    (h : o.luiBoundary s input w rd imm) :
    o.luiFields s input w rd imm := h.1

theorem RvfiObservation.luiBoundary_semantic
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (rd : Reg) (imm : Word)
    (h : o.luiBoundary s input w rd imm) :
    o.toRetirement? = some (luiRetirement s input rd imm) := h.2

theorem RvfiObservation.luiBoundary_rvMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (rd : Reg) (imm : Word)
    (h : o.luiBoundary s input w rd imm) :
    (rvMachineWith profile).step s input =
      (luiNext s rd imm, luiRetirement s input rd imm) := by
  rcases h.1 with
    ⟨hirq, hfetched, hdecode, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hinput : input =
      { fetched := .word w, memory := input.memory, irq := 0 } := by
    cases input with
    | mk fetched memory irq =>
        simp_all
  rw [hinput]
  exact rvMachineWith_lui profile s input.memory w rd imm hdecode

theorem RvfiObservation.luiBoundary_rvMemoryMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (rd : Reg) (imm : Word)
    (h : o.luiBoundary s input w rd imm) :
    (rvMemoryMachineWith profile).step { arch := s, memory := input.memory } input =
      ({ arch := luiNext s rd imm, memory := input.memory },
        luiRetirement s input rd imm) := by
  rcases h.1 with
    ⟨hirq, hfetched, hdecode, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hinput : input =
      { fetched := .word w, memory := input.memory, irq := 0 } := by
    cases input with
    | mk fetched memory irq =>
        simp_all
  rw [hinput]
  simp only [rvMemoryMachineWith]
  rw [isaStepWith_lui profile s input.memory w rd imm hdecode]
  rfl

/-! ## Core-facing LUI cycle case

The class-specific constructor exposes the raw LUI boundary and delegates the
valid/invalid packed-row dispatch to the generic threaded-memory theorem. -/

theorem rvfiCycleStepRefines_of_lui_memory
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hinit : rel machine.init (rvMemoryMachineWith profile).init)
    (hstep : ∀ (state : State) (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ w rd imm,
          input.memory = memoryState.memory ∧
          observation.luiBoundary memoryState.arch input w rd imm ∧
          rel state'
            { arch := luiNext memoryState.arch rd imm,
              memory := memoryState.memory }
      else rel state' memoryState) :
    RvfiCycleStepRefines machine (rvMemoryMachineWith profile) rel admit := by
  refine rvfiCycleStepRefines_of_memory_step profile machine rel admit hinit ?_
  intro state memoryState input hrel hadmit
  have hcase := hstep state memoryState input hrel hadmit
  rcases hmachine : machine.step state input with ⟨state', observation⟩
  simp only [hmachine] at hcase ⊢
  by_cases hv : observation.valid = true
  · have hcase' : ∃ w rd imm,
        input.memory = memoryState.memory ∧
        observation.luiBoundary memoryState.arch input w rd imm ∧
        rel state'
          { arch := luiNext memoryState.arch rd imm,
            memory := memoryState.memory } := by
      simpa [hv] using hcase
    rcases hcase' with ⟨w, rd, imm, hmem, hboundary, hrel'⟩
    have hwell : observation.wellFormed := by
      exact hboundary.1.2.2.2.2.1
    have hto : observation.toRetirement =
        luiRetirement memoryState.arch input rd imm := by
      have hsome := observation.toRetirement?_eq_some hv hwell
      exact Option.some.inj (hsome.symm.trans hboundary.2)
    have hstate : memoryState =
        { arch := memoryState.arch, memory := input.memory } := by
      cases memoryState with
      | mk arch memory => simp [hmem]
    have hstepLui := observation.luiBoundary_rvMemoryMachineWith
      profile memoryState.arch input w rd imm hboundary
    have hstepLui' :
        (rvMemoryMachineWith profile).step memoryState input =
          ({ arch := luiNext memoryState.arch rd imm,
             memory := memoryState.memory },
            luiRetirement memoryState.arch input rd imm) := by
      rw [hstate]
      simpa [hmem] using hstepLui
    simp only [hv]
    exact ⟨_, luiRetirement memoryState.arch input rd imm, hmem, hwell,
      hto, hstepLui', hrel'⟩
  · have hv' : observation.valid = false := by
      cases hvalue : observation.valid with
      | false => exact rfl
      | true => exact False.elim (hv hvalue)
    have hrel' : rel state' memoryState := by
      simpa [hv, hv'] using hcase
    simp only [hv]
    exact hrel'

#print axioms LeanModels.Refine.RvfiObservation.luiBoundary
#print axioms LeanModels.Refine.RvfiObservation.luiBoundary_rvMachineWith
#print axioms LeanModels.Refine.RvfiObservation.luiBoundary_rvMemoryMachineWith
#print axioms LeanModels.Refine.rvfiCycleStepRefines_of_lui_memory

end LeanModels.Refine
