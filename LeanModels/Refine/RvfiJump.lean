import LeanModels.Refine.RvfiMem
import LeanModels.Refine.Rv32iJump

/-!
# Raw RVFI jump boundaries

The `.jump` family has two decoded shapes.  JAL is pc-relative and has no
register source; JALR reads `rs1` and clears the target's low bit.  Both
contracts keep those wire facts explicit before the generic threaded-memory
cycle boundary consumes them.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## Raw JAL predicate -/

def RvfiObservation.jalFields (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (rd : Reg) (offset : Word) : Prop :=
  input.irq = 0 ∧
  input.fetched = .word w ∧
  Fetched.decode (.word w) = some (.jump rd .pc offset) ∧
  o.valid = true ∧
  o.wellFormed ∧
  o.insn = w ∧
  o.pcRdata = s.pc ∧
  o.pcWdata = s.pc + offset ∧
  o.rs1Addr = 0 ∧
  o.rs1Rdata = 0 ∧
  o.rdAddr = rd ∧
  o.rdWdata = s.pc + 4 ∧
  o.trap = false ∧
  o.intr = false ∧
  o.memRmask = 0 ∧
  o.memWmask = 0 ∧
  o.cause = none

def RvfiObservation.jalBoundary (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (rd : Reg) (offset : Word) : Prop :=
  o.jalFields s input w rd offset ∧
  o.toRetirement? = some (jalRetirement s input rd offset)

theorem RvfiObservation.jalBoundary_fields
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (rd : Reg) (offset : Word)
    (h : o.jalBoundary s input w rd offset) :
    o.jalFields s input w rd offset := h.1

theorem RvfiObservation.jalBoundary_semantic
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (rd : Reg) (offset : Word)
    (h : o.jalBoundary s input w rd offset) :
    o.toRetirement? = some (jalRetirement s input rd offset) := h.2

theorem RvfiObservation.jalBoundary_rvMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (rd : Reg) (offset : Word)
    (h : o.jalBoundary s input w rd offset) :
    (rvMachineWith profile).step s input =
      (jalNext s rd offset, jalRetirement s input rd offset) := by
  have hirq := h.1.1
  have hfetched := h.1.2.1
  have hdecode := h.1.2.2.1
  have hinput : input =
      { fetched := .word w, memory := input.memory, irq := 0 } := by
    cases input with
    | mk fetched memory irq =>
        simp_all
  rw [hinput]
  exact rvMachineWith_jal profile s input.memory w rd offset hdecode

theorem RvfiObservation.jalBoundary_rvMemoryMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (rd : Reg) (offset : Word)
    (h : o.jalBoundary s input w rd offset) :
    (rvMemoryMachineWith profile).step
        { arch := s, memory := input.memory } input =
      ({ arch := jalNext s rd offset, memory := input.memory },
        jalRetirement s input rd offset) := by
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
  rw [isaStepWith_jal profile s input.memory w rd offset hdecode]
  rfl

/-! ## Core-facing JAL cycle case -/

theorem rvfiCycleStepRefines_of_jal_memory
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hinit : rel machine.init (rvMemoryMachineWith profile).init)
    (hstep : ∀ (state : State) (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ w rd offset,
          input.memory = memoryState.memory ∧
          observation.jalBoundary memoryState.arch input w rd offset ∧
          rel state'
            { arch := jalNext memoryState.arch rd offset,
              memory := memoryState.memory }
      else rel state' memoryState) :
    RvfiCycleStepRefines machine (rvMemoryMachineWith profile) rel admit := by
  refine rvfiCycleStepRefines_of_memory_step profile machine rel admit hinit ?_
  intro state memoryState input hrel hadmit
  have hcase := hstep state memoryState input hrel hadmit
  rcases hmachine : machine.step state input with ⟨state', observation⟩
  simp only [hmachine] at hcase ⊢
  by_cases hv : observation.valid = true
  · have hcase' : ∃ w rd offset,
        input.memory = memoryState.memory ∧
        observation.jalBoundary memoryState.arch input w rd offset ∧
        rel state'
          { arch := jalNext memoryState.arch rd offset,
            memory := memoryState.memory } := by
      simpa [hv] using hcase
    rcases hcase' with ⟨w, rd, offset, hmem, hboundary, hrel'⟩
    have hwell : observation.wellFormed := by
      exact hboundary.1.2.2.2.2.1
    have hto : observation.toRetirement =
        jalRetirement memoryState.arch input rd offset := by
      have hsome := observation.toRetirement?_eq_some hv hwell
      exact Option.some.inj (hsome.symm.trans hboundary.2)
    have hstate : memoryState =
        { arch := memoryState.arch, memory := input.memory } := by
      cases memoryState with
      | mk arch memory => simp [hmem]
    have hstepJal := observation.jalBoundary_rvMemoryMachineWith
      profile memoryState.arch input w rd offset hboundary
    have hstepJal' :
        (rvMemoryMachineWith profile).step memoryState input =
          ({ arch := jalNext memoryState.arch rd offset,
             memory := memoryState.memory },
            jalRetirement memoryState.arch input rd offset) := by
      rw [hstate]
      simpa [hmem] using hstepJal
    simp only [hv]
    exact ⟨_, jalRetirement memoryState.arch input rd offset, hmem, hwell,
      hto, hstepJal', hrel'⟩
  · have hv' : observation.valid = false := by
      cases hvalue : observation.valid with
      | false => exact rfl
      | true => exact False.elim (hv hvalue)
    have hrel' : rel state' memoryState := by
      simpa [hv, hv'] using hcase
    simp only [hv]
    exact hrel'

/-! ## Raw JALR predicate -/

def RvfiObservation.jalrFields (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (rd rs1 : Reg) (offset : Word) : Prop :=
  input.irq = 0 ∧
  input.fetched = .word w ∧
  Fetched.decode (.word w) = some (.jump rd (.reg rs1) offset) ∧
  o.valid = true ∧
  o.wellFormed ∧
  o.insn = w ∧
  o.pcRdata = s.pc ∧
  o.pcWdata = jalrTarget s rs1 offset ∧
  o.rs1Addr = rs1 ∧
  o.rs1Rdata = s.readReg rs1 ∧
  o.rdAddr = rd ∧
  o.rdWdata = s.pc + 4 ∧
  o.trap = false ∧
  o.intr = false ∧
  o.memRmask = 0 ∧
  o.memWmask = 0 ∧
  o.cause = none

def RvfiObservation.jalrBoundary (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (rd rs1 : Reg) (offset : Word) : Prop :=
  o.jalrFields s input w rd rs1 offset ∧
  o.toRetirement? = some (jalrRetirement s input rd rs1 offset)

theorem RvfiObservation.jalrBoundary_fields
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (rd rs1 : Reg) (offset : Word)
    (h : o.jalrBoundary s input w rd rs1 offset) :
    o.jalrFields s input w rd rs1 offset := h.1

theorem RvfiObservation.jalrBoundary_semantic
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (rd rs1 : Reg) (offset : Word)
    (h : o.jalrBoundary s input w rd rs1 offset) :
    o.toRetirement? = some (jalrRetirement s input rd rs1 offset) := h.2

theorem RvfiObservation.jalrBoundary_rvMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (rd rs1 : Reg) (offset : Word)
    (h : o.jalrBoundary s input w rd rs1 offset) :
    (rvMachineWith profile).step s input =
      (jalrNext s rd rs1 offset, jalrRetirement s input rd rs1 offset) := by
  have hirq := h.1.1
  have hfetched := h.1.2.1
  have hdecode := h.1.2.2.1
  have hinput : input =
      { fetched := .word w, memory := input.memory, irq := 0 } := by
    cases input with
    | mk fetched memory irq =>
        simp_all
  rw [hinput]
  exact rvMachineWith_jalr profile s input.memory w rd rs1 offset hdecode

theorem RvfiObservation.jalrBoundary_rvMemoryMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (rd rs1 : Reg) (offset : Word)
    (h : o.jalrBoundary s input w rd rs1 offset) :
    (rvMemoryMachineWith profile).step
        { arch := s, memory := input.memory } input =
      ({ arch := jalrNext s rd rs1 offset, memory := input.memory },
        jalrRetirement s input rd rs1 offset) := by
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
  rw [isaStepWith_jalr profile s input.memory w rd rs1 offset hdecode]
  rfl

/-! ## Core-facing JALR cycle case -/

theorem rvfiCycleStepRefines_of_jalr_memory
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hinit : rel machine.init (rvMemoryMachineWith profile).init)
    (hstep : ∀ (state : State) (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ w rd rs1 offset,
          input.memory = memoryState.memory ∧
          observation.jalrBoundary memoryState.arch input w rd rs1 offset ∧
          rel state'
            { arch := jalrNext memoryState.arch rd rs1 offset,
              memory := memoryState.memory }
      else rel state' memoryState) :
    RvfiCycleStepRefines machine (rvMemoryMachineWith profile) rel admit := by
  refine rvfiCycleStepRefines_of_memory_step profile machine rel admit hinit ?_
  intro state memoryState input hrel hadmit
  have hcase := hstep state memoryState input hrel hadmit
  rcases hmachine : machine.step state input with ⟨state', observation⟩
  simp only [hmachine] at hcase ⊢
  by_cases hv : observation.valid = true
  · have hcase' : ∃ w rd rs1 offset,
        input.memory = memoryState.memory ∧
        observation.jalrBoundary memoryState.arch input w rd rs1 offset ∧
        rel state'
          { arch := jalrNext memoryState.arch rd rs1 offset,
            memory := memoryState.memory } := by
      simpa [hv] using hcase
    rcases hcase' with ⟨w, rd, rs1, offset, hmem, hboundary, hrel'⟩
    have hwell : observation.wellFormed := by
      exact hboundary.1.2.2.2.2.1
    have hto : observation.toRetirement =
        jalrRetirement memoryState.arch input rd rs1 offset := by
      have hsome := observation.toRetirement?_eq_some hv hwell
      exact Option.some.inj (hsome.symm.trans hboundary.2)
    have hstate : memoryState =
        { arch := memoryState.arch, memory := input.memory } := by
      cases memoryState with
      | mk arch memory => simp [hmem]
    have hstepJalr := observation.jalrBoundary_rvMemoryMachineWith
      profile memoryState.arch input w rd rs1 offset hboundary
    have hstepJalr' :
        (rvMemoryMachineWith profile).step memoryState input =
          ({ arch := jalrNext memoryState.arch rd rs1 offset,
             memory := memoryState.memory },
            jalrRetirement memoryState.arch input rd rs1 offset) := by
      rw [hstate]
      simpa [hmem] using hstepJalr
    simp only [hv]
    exact ⟨_, jalrRetirement memoryState.arch input rd rs1 offset, hmem, hwell,
      hto, hstepJalr', hrel'⟩
  · have hv' : observation.valid = false := by
      cases hvalue : observation.valid with
      | false => exact rfl
      | true => exact False.elim (hv hvalue)
    have hrel' : rel state' memoryState := by
      simpa [hv, hv'] using hcase
    simp only [hv]
    exact hrel'

#print axioms LeanModels.Refine.RvfiObservation.jalBoundary
#print axioms LeanModels.Refine.RvfiObservation.jalBoundary_rvMachineWith
#print axioms LeanModels.Refine.RvfiObservation.jalBoundary_rvMemoryMachineWith
#print axioms LeanModels.Refine.rvfiCycleStepRefines_of_jal_memory
#print axioms LeanModels.Refine.RvfiObservation.jalrBoundary
#print axioms LeanModels.Refine.RvfiObservation.jalrBoundary_rvMachineWith
#print axioms LeanModels.Refine.RvfiObservation.jalrBoundary_rvMemoryMachineWith
#print axioms LeanModels.Refine.rvfiCycleStepRefines_of_jalr_memory

end LeanModels.Refine
