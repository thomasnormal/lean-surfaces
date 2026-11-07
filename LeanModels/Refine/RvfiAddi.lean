import LeanModels.Refine.Rv32i
import LeanModels.Refine.Rvfi

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

#print axioms LeanModels.Refine.addiEffects_no_memory
#print axioms LeanModels.Refine.addiRetirement_no_memory
#print axioms LeanModels.Refine.addiNext_preserves_x0
#print axioms LeanModels.Refine.addiNext_preserves_WF
#print axioms LeanModels.Refine.RvfiObservation.addiBoundary

end LeanModels.Refine
