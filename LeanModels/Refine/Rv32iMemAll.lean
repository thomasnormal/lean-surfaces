import LeanModels.Refine.Rv32iMem

/-!
# Generic RV32I memory retirement boundary

The RV32I data-memory forms differ only in direction, width, and load
signedness.  `MemOp` keeps those semantic choices explicit while sharing the
address, pc, architectural-state, and threaded-memory equations for byte,
halfword, and word accesses.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## Memory operation shape -/

/-- A decoded RV32I load or store, with the exact width and load extension. -/
inductive MemOp where
  | load (signed : Bool) (width : MemW)
  | store (width : MemW)
  deriving DecidableEq, Repr

/-- The corresponding architectural memory direction. -/
def MemOp.toDir : MemOp → MemDir
  | .load signed _ => .load signed
  | .store _ => .store

/-- The byte width carried by the operation. -/
def MemOp.width : MemOp → MemW
  | .load _ width => width
  | .store width => width

/-- The decoded instruction represented by a memory operation. -/
def MemOp.toInstr (kind : MemOp) (r rs1 : Reg) (imm : Word) : Instr :=
  .mem kind.toDir kind.width r rs1 imm

/-! ## Architectural memory equations -/

/-- The architectural state after one RV32I memory operation. -/
def memNext (s : ArchState) (mem : Memory) (kind : MemOp)
    (r rs1 : Reg) (imm : Word) : ArchState :=
  match kind with
  | .load signed width =>
      { s.writeReg r (loadVal mem width signed (s.readReg rs1 + imm)) with
          pc := s.pc + 4 }
  | .store _ =>
      { s with pc := s.pc + 4 }

/-- The architectural effects after one RV32I memory operation. -/
def memEffects (s : ArchState) (kind : MemOp)
    (r rs1 : Reg) (imm : Word) : StepEffects :=
  match kind with
  | .load _ width =>
      { pcTarget := s.pc + 4
        mem := some (.read (s.readReg rs1 + imm) width) }
  | .store width =>
      { pcTarget := s.pc + 4
        mem := some (.write (s.readReg rs1 + imm) width (s.readReg r)) }

/-- The threaded byte memory after one RV32I memory operation. -/
def memAfter (mem : Memory) (s : ArchState) (kind : MemOp)
    (r rs1 : Reg) (imm : Word) : Memory :=
  match kind with
  | .load _ _ => mem
  | .store width => storeVal mem width (s.readReg rs1 + imm) (s.readReg r)

/-- The exact ISA-side boundary contract for a generic memory parcel. -/
def memRetirement (s : ArchState) (input : Input) (kind : MemOp)
    (r rs1 : Reg) (imm : Word) : Retirement :=
  Retirement.ofRvStep s input (memNext s input.memory kind r rs1 imm)
    (memEffects s kind r rs1 imm)

/-- Every profile takes one non-trapping ISA step for a decoded RV32I memory
operation when interrupts are absent. -/
theorem isaStepWith_mem (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (kind : MemOp) (r rs1 : Reg) (imm : Word)
    (hdecode : Fetched.decode (.word w) =
      some (kind.toInstr r rs1 imm)) :
    isaStepWith profile s mem (.word w) 0 =
      (memNext s mem kind r rs1 imm, memEffects s kind r rs1 imm) := by
  have hirq : takeInterrupt? s.csrs 0 = none := by
    simp [takeInterrupt?, pendingSet, selectIrq, irqPriority]
  simp only [isaStepWith, hirq, hdecode]
  cases kind <;> simp [MemOp.toInstr, MemOp.toDir, MemOp.width, memNext,
    memEffects, execInstr, Fetched.size]

/-- The memory-threaded ISA step applies stores and leaves loads' memory view
unchanged. -/
theorem isaStepMemWith_mem (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (kind : MemOp) (r rs1 : Reg) (imm : Word)
    (hdecode : Fetched.decode (.word w) =
      some (kind.toInstr r rs1 imm)) :
    isaStepMemWith profile s mem (.word w) 0 =
      (memNext s mem kind r rs1 imm, memAfter mem s kind r rs1 imm) := by
  unfold isaStepMemWith
  rw [isaStepWith_mem profile s mem w kind r rs1 imm hdecode]
  cases kind <;> rfl

/-- The generic machine adapter exposes the same memory commit boundary. -/
theorem rvMachineWith_mem (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (kind : MemOp) (r rs1 : Reg) (imm : Word)
    (hdecode : Fetched.decode (.word w) =
      some (kind.toInstr r rs1 imm)) :
    (rvMachineWith profile).step s
        { fetched := .word w, memory := mem, irq := 0 } =
      (memNext s mem kind r rs1 imm,
        memRetirement s { fetched := .word w, memory := mem, irq := 0 }
          kind r rs1 imm) := by
  simp only [rvMachineWith]
  rw [isaStepWith_mem profile s mem w kind r rs1 imm hdecode]
  rfl

#print axioms LeanModels.Refine.isaStepWith_mem
#print axioms LeanModels.Refine.isaStepMemWith_mem
#print axioms LeanModels.Refine.rvMachineWith_mem

end LeanModels.Refine
