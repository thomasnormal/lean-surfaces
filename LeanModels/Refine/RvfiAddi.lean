import LeanModels.Refine.Rv32i
import LeanModels.Refine.Rvfi
import LeanModels.Refine.MemoryMachine

/-!
# Raw RVFI ADDI boundary

The generic RVFI adapter turns a well-formed wire row into a semantic
`Retirement`.  This file gives a core proof one reusable predicate for the
raw row emitted by a 32-bit, interrupt-free `ADDI`.  The predicate keeps the
wire facts visible (including the fetched word, source read, destination
write, and the two memory masks) and separately records equality with the
architectural `addiRetirement`.

The semantic equality is intentional.  `Retirement.ofRvStep` records register
changes, while an RVFI row carries the writeback bus; a core proof must show
that its row agrees with the commit abstraction for the particular state.
This prevents the boundary from silently inventing a write when the
architectural value is unchanged.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## Architectural facts shared by every ADDI boundary -/

/-- ADDI has no data-memory effect in the architectural step. -/
@[simp] theorem addiEffects_no_memory (s : ArchState) :
    (addiEffects s).mem = none := rfl

/-- The commit produced by an ADDI carries no data-memory effect. -/
@[simp] theorem addiRetirement_no_memory (s : ArchState) (input : Input)
    (rd rs1 : Reg) (imm : Word) :
    (addiRetirement s input rd rs1 imm).memory = none := rfl

/-- `writeReg` preserves the architectural x0 slot, including when the
destination of the ADDI is x0. -/
theorem addiNext_preserves_x0 (s : ArchState) (rd rs1 : Reg) (imm : Word) :
    (addiNext s rd rs1 imm).readReg 0 = s.readReg 0 := by
  by_cases hrd : rd = 0
  · simp [addiNext, ArchState.readReg, ArchState.writeReg, hrd]
  ·
    have h0rd : (0 : Reg) ≠ rd := by
      intro h
      exact hrd h.symm
    simp [addiNext, ArchState.readReg, ArchState.writeReg, hrd, h0rd]

/-- A well-formed architectural state keeps x0 equal to zero after ADDI. -/
theorem addiNext_preserves_WF (s : ArchState) (rd rs1 : Reg) (imm : Word)
    (hWF : s.WF) : (addiNext s rd rs1 imm).WF := by
  have hx0 := addiNext_preserves_x0 s rd rs1 imm
  simpa [ArchState.WF, ArchState.readReg] using hx0.trans hWF

/-! ## The raw wire predicate -/

/-- The raw RVFI facts for a 32-bit ADDI.

`input.fetched` is required to be the same word reported by RVFI, and its
decode is part of the predicate rather than an unstated side condition.  The
interrupt input and both trap indicators are zero; mode/XLEN and mask
well-formedness are retained through `o.wellFormed`.  `rdWdataValid` is left
to the semantic equality below: the commit adapter decides whether the
architectural register change is observable in `writes`.
-/
def RvfiObservation.addiFields (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (rd rs1 : Reg) (imm : Word) : Prop :=
  input.irq = 0 ∧
  input.fetched = .word w ∧
  Fetched.decode (.word w) =
    some (.alu .add rd (.reg rs1) (.imm imm)) ∧
  o.valid = true ∧
  o.wellFormed ∧
  o.insn = w ∧
  o.pcRdata = s.pc ∧
  o.pcWdata = s.pc + 4 ∧
  o.rs1Addr = rs1 ∧
  o.rs1Rdata = s.readReg rs1 ∧
  o.rdAddr = rd ∧
  o.rdWdata = s.readReg rs1 + imm ∧
  o.trap = false ∧
  o.intr = false ∧
  o.memRmask = 0 ∧
  o.memWmask = 0 ∧
  o.cause = none

/-- A raw RVFI ADDI row together with its semantic commit equality. -/
def RvfiObservation.addiBoundary (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (rd rs1 : Reg) (imm : Word) : Prop :=
  o.addiFields s input w rd rs1 imm ∧
  o.toRetirement? = some (addiRetirement s input rd rs1 imm)

theorem RvfiObservation.addiBoundary_fields
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (rd rs1 : Reg) (imm : Word)
    (h : o.addiBoundary s input w rd rs1 imm) :
    o.addiFields s input w rd rs1 imm := h.1

theorem RvfiObservation.addiBoundary_semantic
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (rd rs1 : Reg) (imm : Word)
    (h : o.addiBoundary s input w rd rs1 imm) :
    o.toRetirement? = some (addiRetirement s input rd rs1 imm) := h.2

theorem RvfiObservation.addiBoundary_no_trap
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (rd rs1 : Reg) (imm : Word)
    (h : o.addiBoundary s input w rd rs1 imm) :
    o.trap = false ∧ o.intr = false ∧ o.cause = none := by
  rcases h.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, htrap, hintr, _, _, hc⟩
  exact ⟨htrap, hintr, hc⟩

theorem RvfiObservation.addiBoundary_no_memory_masks
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (rd rs1 : Reg) (imm : Word)
    (h : o.addiBoundary s input w rd rs1 imm) :
    o.memRmask = 0 ∧ o.memWmask = 0 := by
  rcases h.1 with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hrmask, hwmask, _⟩
  exact ⟨hrmask, hwmask⟩

theorem RvfiObservation.addiBoundary_memory_none
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (rd rs1 : Reg) (imm : Word)
    (_h : o.addiBoundary s input w rd rs1 imm) :
    (addiRetirement s input rd rs1 imm).memory = none := by
  exact addiRetirement_no_memory s input rd rs1 imm

theorem RvfiObservation.addiBoundary_x0
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (rd rs1 : Reg) (imm : Word)
    (_h : o.addiBoundary s input w rd rs1 imm) :
    (addiNext s rd rs1 imm).readReg 0 = s.readReg 0 := by
  exact addiNext_preserves_x0 s rd rs1 imm

/-- A raw ADDI boundary supplies the exact one-step architectural memory
equation needed by a core invariant. -/
theorem RvfiObservation.addiBoundary_isaStepMemWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (rd rs1 : Reg) (imm : Word)
    (h : o.addiBoundary s input w rd rs1 imm) :
    isaStepMemWith profile s input.memory input.fetched input.irq =
      (addiNext s rd rs1 imm, input.memory) := by
  rcases h.1 with ⟨hirq, hfetched, hdecode, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  simpa [hirq, hfetched] using
    (isaStepMemWith_addi profile s input.memory w rd rs1 imm hdecode)

/-- The same raw boundary exposes the generic machine adapter's commit, so a
future loaded-core proof can compare its RVFI row directly with `rvMachineWith`.
-/
theorem RvfiObservation.addiBoundary_rvMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (rd rs1 : Reg) (imm : Word)
    (h : o.addiBoundary s input w rd rs1 imm) :
    (rvMachineWith profile).step s input =
      (addiNext s rd rs1 imm, addiRetirement s input rd rs1 imm) := by
  rcases h.1 with ⟨hirq, hfetched, hdecode, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hinput : input =
      { fetched := .word w, memory := input.memory, irq := 0 } := by
    cases input with
    | mk fetched memory irq =>
        simp_all
  rw [hinput]
  exact rvMachineWith_addi profile s input.memory w rd rs1 imm hdecode

/- The same raw boundary drives the memory-threaded machine.  ADDI has no
data-memory effect, so the stateful memory remains exactly the input view. -/
theorem RvfiObservation.addiBoundary_rvMemoryMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (rd rs1 : Reg) (imm : Word)
    (h : o.addiBoundary s input w rd rs1 imm) :
    (rvMemoryMachineWith profile).step { arch := s, memory := input.memory } input =
      ({ arch := addiNext s rd rs1 imm, memory := input.memory },
        addiRetirement s input rd rs1 imm) := by
  rcases h.1 with ⟨hirq, hfetched, hdecode, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩
  have hinput : input =
      { fetched := .word w, memory := input.memory, irq := 0 } := by
    cases input with
    | mk fetched memory irq =>
        simp_all
  rw [hinput]
  simp only [rvMemoryMachineWith]
  rw [isaStepWith_addi profile s input.memory w rd rs1 imm hdecode]
  rfl

/-! ## A core-facing ADDI cycle case

The first loaded-core milestone is an inductive invariant whose valid RVFI
cycles are ADDI rows.  This constructor packages that instruction-class case
directly into the strict raw RVFI contract; the core-specific state relation
and the per-cycle ADDI boundary remain explicit hypotheses. -/

theorem rvfiCycleStepRefines_of_addi
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → ArchState → Prop) (admit : Input → Prop)
    (hinit : rel machine.init (rvMachineWith profile).init)
    (hstep : ∀ (state : State) (arch : ArchState) (input : Input),
      rel state arch → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ w rd rs1 imm,
          observation.addiBoundary arch input w rd rs1 imm ∧
          rel state' (addiNext arch rd rs1 imm)
      else rel state' arch) :
    RvfiCycleStepRefines machine (rvMachineWith profile) rel admit := by
  apply rvfiCycleStepRefines_of_step hinit
  intro state arch input hrel hadmit
  have hcase := hstep state arch input hrel hadmit
  rcases hmachine : machine.step state input with ⟨state', observation⟩
  simp only [hmachine] at hcase
  rcases hisa : (rvMachineWith profile).step arch input with
    ⟨arch', retirement⟩
  simp only
  change (observation.valid = true ∧ observation.wellFormed ∧
      rel state' arch' ∧ observation.toRetirement = retirement) ∨
    (observation.valid = false ∧ rel state' arch)
  by_cases hv : observation.valid = true
  · have hcase' : ∃ w rd rs1 imm,
        observation.addiBoundary arch input w rd rs1 imm ∧
        rel state' (addiNext arch rd rs1 imm) := by
      simpa [hv] using hcase
    rcases hcase' with ⟨w, rd, rs1, imm, hboundary, hrel'⟩
    have hwell : observation.wellFormed := by
      rcases hboundary.1 with
        ⟨_, _, _, _, hwell, _, _, _, _, _, _, _, _, _, _, _, _⟩
      exact hwell
    have hto : observation.toRetirement =
        addiRetirement arch input rd rs1 imm := by
      have hsome := observation.toRetirement?_eq_some hv hwell
      exact Option.some.inj (hsome.symm.trans hboundary.2)
    have hstepAddi := observation.addiBoundary_rvMachineWith
      profile arch input w rd rs1 imm hboundary
    have hpair : (arch', retirement) =
        (addiNext arch rd rs1 imm,
          addiRetirement arch input rd rs1 imm) := by
      rw [← hisa, hstepAddi]
    have harch' : arch' = addiNext arch rd rs1 imm := congrArg Prod.fst hpair
    have hretirement : retirement =
        addiRetirement arch input rd rs1 imm := congrArg Prod.snd hpair
    rw [harch', hretirement]
    left
    exact ⟨hv, hwell, hrel', hto⟩
  · have hv' : observation.valid = false := by
      cases hvalue : observation.valid with
      | false => exact rfl
      | true => exact False.elim (hv hvalue)
    have hrel' : rel state' arch := by
      simpa [hv, hv'] using hcase
    right
    exact ⟨hv', hrel'⟩

/-! ## Memory-threaded ADDI cycle case

The stateful architectural machine carries the byte memory between
retirements.  This constructor keeps the raw input-memory equality explicit,
so an invariant cannot silently compare an RVFI row against a different
memory view. -/

theorem rvfiCycleStepRefines_of_addi_memory
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → RvMemoryState → Prop) (admit : Input → Prop)
    (hinit : rel machine.init (rvMemoryMachineWith profile).init)
    (hstep : ∀ (state : State) (memoryState : RvMemoryState) (input : Input),
      rel state memoryState → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ w rd rs1 imm,
          input.memory = memoryState.memory ∧
          observation.addiBoundary memoryState.arch input w rd rs1 imm ∧
          rel state'
            { arch := addiNext memoryState.arch rd rs1 imm,
              memory := memoryState.memory }
      else rel state' memoryState) :
    RvfiCycleStepRefines machine (rvMemoryMachineWith profile) rel admit := by
  apply rvfiCycleStepRefines_of_step hinit
  intro state memoryState input hrel hadmit
  have hcase := hstep state memoryState input hrel hadmit
  rcases hmachine : machine.step state input with ⟨state', observation⟩
  simp only [hmachine] at hcase
  rcases hisa : (rvMemoryMachineWith profile).step memoryState input with
    ⟨memoryState', retirement⟩
  simp only
  change (observation.valid = true ∧ observation.wellFormed ∧
      rel state' memoryState' ∧ observation.toRetirement = retirement) ∨
    (observation.valid = false ∧ rel state' memoryState)
  by_cases hv : observation.valid = true
  · have hcase' : ∃ w rd rs1 imm,
        input.memory = memoryState.memory ∧
        observation.addiBoundary memoryState.arch input w rd rs1 imm ∧
        rel state'
          { arch := addiNext memoryState.arch rd rs1 imm,
            memory := memoryState.memory } := by
      simpa [hv] using hcase
    rcases hcase' with ⟨w, rd, rs1, imm, hmem, hboundary, hrel'⟩
    have hwell : observation.wellFormed := by
      exact hboundary.1.2.2.2.2.1
    have hto : observation.toRetirement =
        addiRetirement memoryState.arch input rd rs1 imm := by
      have hsome := observation.toRetirement?_eq_some hv hwell
      exact Option.some.inj (hsome.symm.trans hboundary.2)
    have hstate : memoryState =
        { arch := memoryState.arch, memory := input.memory } := by
      cases memoryState with
      | mk arch memory => simp [hmem]
    have hstepAddi := observation.addiBoundary_rvMemoryMachineWith
      profile memoryState.arch input w rd rs1 imm hboundary
    have hstepAddi' :
        (rvMemoryMachineWith profile).step memoryState input =
          ({ arch := addiNext memoryState.arch rd rs1 imm,
             memory := memoryState.memory },
            addiRetirement memoryState.arch input rd rs1 imm) := by
      rw [hstate]
      simpa [hmem] using hstepAddi
    have hpair : (memoryState', retirement) =
        ({ arch := addiNext memoryState.arch rd rs1 imm,
           memory := memoryState.memory },
          addiRetirement memoryState.arch input rd rs1 imm) := by
      rw [← hisa, hstepAddi']
    have hstate' : memoryState' =
        { arch := addiNext memoryState.arch rd rs1 imm,
          memory := memoryState.memory } := congrArg Prod.fst hpair
    have hretirement : retirement =
        addiRetirement memoryState.arch input rd rs1 imm :=
      congrArg Prod.snd hpair
    rw [hstate', hretirement]
    left
    exact ⟨hv, hwell, hrel', hto⟩
  · have hv' : observation.valid = false := by
      cases hvalue : observation.valid with
      | false => exact rfl
      | true => exact False.elim (hv hvalue)
    have hrel' : rel state' memoryState := by
      simpa [hv, hv'] using hcase
    right
    exact ⟨hv', hrel'⟩

#print axioms LeanModels.Refine.addiEffects_no_memory
#print axioms LeanModels.Refine.addiRetirement_no_memory
#print axioms LeanModels.Refine.addiNext_preserves_x0
#print axioms LeanModels.Refine.addiNext_preserves_WF
#print axioms LeanModels.Refine.RvfiObservation.addiBoundary
#print axioms LeanModels.Refine.RvfiObservation.addiBoundary_isaStepMemWith
#print axioms LeanModels.Refine.RvfiObservation.addiBoundary_rvMachineWith
#print axioms LeanModels.Refine.RvfiObservation.addiBoundary_rvMemoryMachineWith
#print axioms LeanModels.Refine.rvfiCycleStepRefines_of_addi
#print axioms LeanModels.Refine.rvfiCycleStepRefines_of_addi_memory

end LeanModels.Refine
