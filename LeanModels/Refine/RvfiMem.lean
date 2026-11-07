import LeanModels.Refine.Rv32iMem
import LeanModels.Refine.RvfiAddi

/-!
# Raw RVFI SW boundary

The measured PicoRV32 store row is kept as one reusable predicate.  It records
the source register values, the decoded word, the exact word write mask and
payload, and equality with the architectural store retirement.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## Raw store predicate -/

def RvfiObservation.swFields (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (rs1 rs2 : Reg) (imm : Word) : Prop :=
  input.irq = 0 ∧
  input.fetched = .word w ∧
  Fetched.decode (.word w) =
    some (.mem .store .word rs2 rs1 imm) ∧
  o.valid = true ∧
  o.wellFormed ∧
  o.insn = w ∧
  o.pcRdata = s.pc ∧
  o.pcWdata = s.pc + 4 ∧
  o.rs1Addr = rs1 ∧
  o.rs1Rdata = s.readReg rs1 ∧
  o.rs2Addr = rs2 ∧
  o.rs2Rdata = s.readReg rs2 ∧
  o.rdWdataValid = false ∧
  o.memAddr = s.readReg rs1 + imm ∧
  o.memRmask = 0 ∧
  o.memWmask = 0b1111 ∧
  o.memWdata = s.readReg rs2 ∧
  o.trap = false ∧
  o.intr = false ∧
  o.cause = none

def RvfiObservation.swBoundary (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (rs1 rs2 : Reg) (imm : Word) : Prop :=
  o.swFields s input w rs1 rs2 imm ∧
  o.toRetirement? = some (swRetirement s input rs1 rs2 imm)

def RvfiObservation.lwFields (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (rd rs1 : Reg) (imm : Word) : Prop :=
  input.irq = 0 ∧
  input.fetched = .word w ∧
  Fetched.decode (.word w) =
    some (.mem (.load true) .word rd rs1 imm) ∧
  o.valid = true ∧
  o.wellFormed ∧
  o.insn = w ∧
  o.pcRdata = s.pc ∧
  o.pcWdata = s.pc + 4 ∧
  o.rs1Addr = rs1 ∧
  o.rs1Rdata = s.readReg rs1 ∧
  o.rdAddr = rd ∧
  o.rdWdata = loadVal input.memory .word false (s.readReg rs1 + imm) ∧
  o.memAddr = s.readReg rs1 + imm ∧
  o.memRmask = 0b1111 ∧
  o.memWmask = 0 ∧
  o.memRdata = loadVal input.memory .word false (s.readReg rs1 + imm) ∧
  o.trap = false ∧
  o.intr = false ∧
  o.cause = none

def RvfiObservation.lwBoundary (s : ArchState) (input : Input)
    (o : RvfiObservation) (w : Word) (rd rs1 : Reg) (imm : Word) : Prop :=
  o.lwFields s input w rd rs1 imm ∧
  o.toRetirement? = some (lwRetirement s input rd rs1 imm)

theorem RvfiObservation.swBoundary_fields
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (rs1 rs2 : Reg) (imm : Word)
    (h : o.swBoundary s input w rs1 rs2 imm) :
    o.swFields s input w rs1 rs2 imm := h.1

theorem RvfiObservation.swBoundary_semantic
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (rs1 rs2 : Reg) (imm : Word)
    (h : o.swBoundary s input w rs1 rs2 imm) :
    o.toRetirement? = some (swRetirement s input rs1 rs2 imm) := h.2

theorem RvfiObservation.lwBoundary_fields
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (rd rs1 : Reg) (imm : Word)
    (h : o.lwBoundary s input w rd rs1 imm) :
    o.lwFields s input w rd rs1 imm := h.1

theorem RvfiObservation.lwBoundary_semantic
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (rd rs1 : Reg) (imm : Word)
    (h : o.lwBoundary s input w rd rs1 imm) :
    o.toRetirement? = some (lwRetirement s input rd rs1 imm) := h.2

theorem RvfiObservation.swBoundary_no_trap
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (rs1 rs2 : Reg) (imm : Word)
    (h : o.swBoundary s input w rs1 rs2 imm) :
    o.trap = false ∧ o.intr = false ∧ o.cause = none := by
  rcases h.1 with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htrap, hintr,
      hcause⟩
  exact ⟨htrap, hintr, hcause⟩

theorem RvfiObservation.swBoundary_memory_masks
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (rs1 rs2 : Reg) (imm : Word)
    (h : o.swBoundary s input w rs1 rs2 imm) :
    o.memRmask = 0 ∧ o.memWmask = 0b1111 ∧
      o.memAddr = s.readReg rs1 + imm ∧
      o.memWdata = s.readReg rs2 := by
  rcases h.1 with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, haddr, hrmask, hwmask,
      hwdata, _, _, _⟩
  exact ⟨hrmask, hwmask, haddr, hwdata⟩

theorem RvfiObservation.lwBoundary_no_trap
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (rd rs1 : Reg) (imm : Word)
    (h : o.lwBoundary s input w rd rs1 imm) :
    o.trap = false ∧ o.intr = false ∧ o.cause = none := by
  rcases h.1 with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htrap, hintr,
      hcause⟩
  exact ⟨htrap, hintr, hcause⟩

theorem RvfiObservation.lwBoundary_memory_masks
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (rd rs1 : Reg) (imm : Word)
    (h : o.lwBoundary s input w rd rs1 imm) :
    o.memRmask = 0b1111 ∧ o.memWmask = 0 ∧
      o.memAddr = s.readReg rs1 + imm ∧
      o.memRdata = loadVal input.memory .word false
        (s.readReg rs1 + imm) := by
  rcases h.1 with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, haddr, hrmask, hwmask, hrdata,
      _, _, _⟩
  exact ⟨hrmask, hwmask, haddr, hrdata⟩

theorem RvfiObservation.swBoundary_state
    (o : RvfiObservation) (s : ArchState) (input : Input)
    (w : Word) (rs1 rs2 : Reg) (imm : Word)
    (_h : o.swBoundary s input w rs1 rs2 imm) (r : Reg) :
    (swNext s).readReg r = s.readReg r :=
  swNext_preserves_regs s r

theorem RvfiObservation.swBoundary_isaStepMemWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (rs1 rs2 : Reg) (imm : Word)
    (h : o.swBoundary s input w rs1 rs2 imm) :
    isaStepMemWith profile s input.memory input.fetched input.irq =
      (swNext s, storeVal input.memory .word
        (s.readReg rs1 + imm) (s.readReg rs2)) := by
  rcases h.1 with
    ⟨hirq, hfetched, hdecode, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _⟩
  simpa [hirq, hfetched] using
    (isaStepMemWith_sw profile s input.memory w rs1 rs2 imm hdecode)

theorem RvfiObservation.lwBoundary_isaStepMemWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (rd rs1 : Reg) (imm : Word)
    (h : o.lwBoundary s input w rd rs1 imm) :
    isaStepMemWith profile s input.memory input.fetched input.irq =
      (lwNext s input.memory rd rs1 imm, input.memory) := by
  rcases h.1 with
    ⟨hirq, hfetched, hdecode, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _⟩
  simpa [hirq, hfetched] using
    (isaStepMemWith_lw profile s input.memory w rd rs1 imm hdecode)

theorem RvfiObservation.swBoundary_rvMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (rs1 rs2 : Reg) (imm : Word)
    (h : o.swBoundary s input w rs1 rs2 imm) :
    (rvMachineWith profile).step s input =
      (swNext s, swRetirement s input rs1 rs2 imm) := by
  rcases h.1 with
    ⟨hirq, hfetched, hdecode, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _⟩
  have hinput : input =
      { fetched := .word w, memory := input.memory, irq := 0 } := by
    cases input with
    | mk fetched memory irq =>
        simp_all
  rw [hinput]
  exact rvMachineWith_sw profile s input.memory w rs1 rs2 imm hdecode

/- The store boundary also drives the memory-threaded machine, exposing the
exact byte-memory update alongside the architectural commit. -/
theorem RvfiObservation.swBoundary_rvMemoryMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (rs1 rs2 : Reg) (imm : Word)
    (h : o.swBoundary s input w rs1 rs2 imm) :
    (rvMemoryMachineWith profile).step { arch := s, memory := input.memory } input =
      ({ arch := swNext s,
          memory := storeVal input.memory .word
            (s.readReg rs1 + imm) (s.readReg rs2) },
        swRetirement s input rs1 rs2 imm) := by
  rcases h.1 with
    ⟨hirq, hfetched, hdecode, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _, _⟩
  have hinput : input =
      { fetched := .word w, memory := input.memory, irq := 0 } := by
    cases input with
    | mk fetched memory irq =>
        simp_all
  rw [hinput]
  simp only [rvMemoryMachineWith]
  rw [isaStepWith_sw profile s input.memory w rs1 rs2 imm hdecode]
  rfl

theorem RvfiObservation.lwBoundary_rvMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (rd rs1 : Reg) (imm : Word)
    (h : o.lwBoundary s input w rd rs1 imm) :
    (rvMachineWith profile).step s input =
      (lwNext s input.memory rd rs1 imm, lwRetirement s input rd rs1 imm) := by
  rcases h.1 with
    ⟨hirq, hfetched, hdecode, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _⟩
  have hinput : input =
      { fetched := .word w, memory := input.memory, irq := 0 } := by
    cases input with
    | mk fetched memory irq =>
        simp_all
  rw [hinput]
  exact rvMachineWith_lw profile s input.memory w rd rs1 imm hdecode

/- A load leaves the threaded byte memory unchanged while retaining the exact
memory view used to compute the destination register. -/
theorem RvfiObservation.lwBoundary_rvMemoryMachineWith
    (profile : PlatformProfile) (o : RvfiObservation) (s : ArchState)
    (input : Input) (w : Word) (rd rs1 : Reg) (imm : Word)
    (h : o.lwBoundary s input w rd rs1 imm) :
    (rvMemoryMachineWith profile).step { arch := s, memory := input.memory } input =
      ({ arch := lwNext s input.memory rd rs1 imm,
          memory := input.memory },
        lwRetirement s input rd rs1 imm) := by
  rcases h.1 with
    ⟨hirq, hfetched, hdecode, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      _⟩
  have hinput : input =
      { fetched := .word w, memory := input.memory, irq := 0 } := by
    cases input with
    | mk fetched memory irq =>
        simp_all
  rw [hinput]
  simp only [rvMemoryMachineWith]
  rw [isaStepWith_lw profile s input.memory w rd rs1 imm hdecode]
  rfl

/-! ## Core-facing store cycle case

The strict packed-cycle contract can consume the measured store row directly.
The relation and input-admission predicate stay abstract so this constructor
can be used by a loaded core once its memory invariant establishes the raw
`SW` fields. -/

theorem rvfiCycleStepRefines_of_sw
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → ArchState → Prop) (admit : Input → Prop)
    (hinit : rel machine.init (rvMachineWith profile).init)
    (hstep : ∀ (state : State) (arch : ArchState) (input : Input),
      rel state arch → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ w rs1 rs2 imm,
          observation.swBoundary arch input w rs1 rs2 imm ∧
          rel state' (swNext arch)
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
  · have hcase' : ∃ w rs1 rs2 imm,
        observation.swBoundary arch input w rs1 rs2 imm ∧
        rel state' (swNext arch) := by
      simpa [hv] using hcase
    rcases hcase' with ⟨w, rs1, rs2, imm, hboundary, hrel'⟩
    have hwell : observation.wellFormed := by
      exact hboundary.1.2.2.2.2.1
    have hto : observation.toRetirement =
        swRetirement arch input rs1 rs2 imm := by
      have hsome := observation.toRetirement?_eq_some hv hwell
      exact Option.some.inj (hsome.symm.trans hboundary.2)
    have hstepSw := observation.swBoundary_rvMachineWith
      profile arch input w rs1 rs2 imm hboundary
    have hpair : (arch', retirement) =
        (swNext arch, swRetirement arch input rs1 rs2 imm) := by
      rw [← hisa, hstepSw]
    have harch' : arch' = swNext arch := congrArg Prod.fst hpair
    have hretirement : retirement =
        swRetirement arch input rs1 rs2 imm := congrArg Prod.snd hpair
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

/-! ## Core-facing load cycle case

The load constructor keeps the memory view in the raw boundary: the valid
case advances through `lwNext` using the input memory and matches the exact
`lwRetirement`, while invalid rows remain architectural bubbles. -/

theorem rvfiCycleStepRefines_of_lw
    {State : Type} (profile : PlatformProfile)
    (machine : RvfiCycleMachine State)
    (rel : State → ArchState → Prop) (admit : Input → Prop)
    (hinit : rel machine.init (rvMachineWith profile).init)
    (hstep : ∀ (state : State) (arch : ArchState) (input : Input),
      rel state arch → admit input →
      let (state', observation) := machine.step state input
      if observation.valid then
        ∃ w rd rs1 imm,
          observation.lwBoundary arch input w rd rs1 imm ∧
          rel state' (lwNext arch input.memory rd rs1 imm)
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
        observation.lwBoundary arch input w rd rs1 imm ∧
        rel state' (lwNext arch input.memory rd rs1 imm) := by
      simpa [hv] using hcase
    rcases hcase' with ⟨w, rd, rs1, imm, hboundary, hrel'⟩
    have hwell : observation.wellFormed := by
      exact hboundary.1.2.2.2.2.1
    have hto : observation.toRetirement =
        lwRetirement arch input rd rs1 imm := by
      have hsome := observation.toRetirement?_eq_some hv hwell
      exact Option.some.inj (hsome.symm.trans hboundary.2)
    have hstepLw := observation.lwBoundary_rvMachineWith
      profile arch input w rd rs1 imm hboundary
    have hpair : (arch', retirement) =
        (lwNext arch input.memory rd rs1 imm,
          lwRetirement arch input rd rs1 imm) := by
      rw [← hisa, hstepLw]
    have harch' : arch' = lwNext arch input.memory rd rs1 imm :=
      congrArg Prod.fst hpair
    have hretirement : retirement =
        lwRetirement arch input rd rs1 imm := congrArg Prod.snd hpair
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

#print axioms LeanModels.Refine.RvfiObservation.swBoundary
#print axioms LeanModels.Refine.RvfiObservation.swBoundary_isaStepMemWith
#print axioms LeanModels.Refine.RvfiObservation.swBoundary_rvMachineWith
#print axioms LeanModels.Refine.RvfiObservation.swBoundary_rvMemoryMachineWith
#print axioms LeanModels.Refine.RvfiObservation.lwBoundary
#print axioms LeanModels.Refine.RvfiObservation.lwBoundary_isaStepMemWith
#print axioms LeanModels.Refine.RvfiObservation.lwBoundary_rvMachineWith
#print axioms LeanModels.Refine.RvfiObservation.lwBoundary_rvMemoryMachineWith
#print axioms LeanModels.Refine.rvfiCycleStepRefines_of_sw
#print axioms LeanModels.Refine.rvfiCycleStepRefines_of_lw

end LeanModels.Refine
