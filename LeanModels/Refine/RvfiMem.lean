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

#print axioms LeanModels.Refine.RvfiObservation.swBoundary
#print axioms LeanModels.Refine.RvfiObservation.swBoundary_isaStepMemWith
#print axioms LeanModels.Refine.RvfiObservation.swBoundary_rvMachineWith
#print axioms LeanModels.Refine.RvfiObservation.swBoundary_rvMemoryMachineWith
#print axioms LeanModels.Refine.RvfiObservation.lwBoundary
#print axioms LeanModels.Refine.RvfiObservation.lwBoundary_isaStepMemWith
#print axioms LeanModels.Refine.RvfiObservation.lwBoundary_rvMachineWith
#print axioms LeanModels.Refine.RvfiObservation.lwBoundary_rvMemoryMachineWith

end LeanModels.Refine
