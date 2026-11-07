import LeanModels.Refine.Rv32i

/-!
# RV32I store boundary

This file adds the architectural contract for the measured `SW` row in the
PicoRV32 trace.  Like the ADDI contract, it is independent of any core state:
a loaded-core proof supplies the raw RVFI facts and consumes the exact ISA
state and memory equations below.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## Architectural store equations -/

/- The architectural state after a 32-bit store. -/
def swNext (s : ArchState) : ArchState :=
  { s with pc := s.pc + 4 }

/- The architectural effects of a 32-bit store. -/
def swEffects (s : ArchState) (rs1 rs2 : Reg) (imm : Word) : StepEffects :=
  { pcTarget := s.pc + 4
    mem := some (.write (s.readReg rs1 + imm) .word (s.readReg rs2)) }

/- The exact ISA-side retirement for a 32-bit store. -/
def swRetirement (s : ArchState) (input : Input)
    (rs1 rs2 : Reg) (imm : Word) : Retirement :=
  Retirement.ofRvStep s input (swNext s) (swEffects s rs1 rs2 imm)

/- The architectural state after a 32-bit unsigned load. -/
def lwNext (s : ArchState) (mem : Memory) (rd rs1 : Reg) (imm : Word) : ArchState :=
  { s.writeReg rd (loadVal mem .word true (s.readReg rs1 + imm)) with
    pc := s.pc + 4 }

/- The architectural effects of a 32-bit unsigned load. -/
def lwEffects (s : ArchState) (rs1 : Reg) (imm : Word) : StepEffects :=
  { pcTarget := s.pc + 4
    mem := some (.read (s.readReg rs1 + imm) .word) }

/- The exact ISA-side retirement for a 32-bit unsigned load. -/
def lwRetirement (s : ArchState) (input : Input)
    (rd rs1 : Reg) (imm : Word) : Retirement :=
  Retirement.ofRvStep s input (lwNext s input.memory rd rs1 imm)
    (lwEffects s rs1 imm)

/- A store changes no architectural register, including x0. -/
theorem swNext_preserves_regs (s : ArchState) (r : Reg) :
    (swNext s).readReg r = s.readReg r := by
  rfl

/- Every profile takes one non-trapping ISA step for a decoded 32-bit SW. -/
theorem isaStepWith_sw (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (rs1 rs2 : Reg) (imm : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.mem .store .word rs2 rs1 imm)) :
    isaStepWith profile s mem (.word w) 0 =
      (swNext s, swEffects s rs1 rs2 imm) := by
  have hirq : takeInterrupt? s.csrs 0 = none := by
    simp [takeInterrupt?, pendingSet, selectIrq, irqPriority]
  simp only [isaStepWith, hirq, hdecode]
  simp [swNext, swEffects, execInstr, Fetched.size]

/- The memory-threaded SW step applies its one word store. -/
theorem isaStepMemWith_sw (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (rs1 rs2 : Reg) (imm : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.mem .store .word rs2 rs1 imm)) :
    isaStepMemWith profile s mem (.word w) 0 =
      (swNext s, storeVal mem .word (s.readReg rs1 + imm) (s.readReg rs2)) := by
  unfold isaStepMemWith
  rw [isaStepWith_sw profile s mem w rs1 rs2 imm hdecode]
  rfl

/- The generic machine adapter exposes the same SW commit boundary. -/
theorem rvMachineWith_sw (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (rs1 rs2 : Reg) (imm : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.mem .store .word rs2 rs1 imm)) :
    (rvMachineWith profile).step s
        { fetched := .word w, memory := mem, irq := 0 } =
      (swNext s, swRetirement s
        { fetched := .word w, memory := mem, irq := 0 } rs1 rs2 imm) := by
  simp only [rvMachineWith]
  rw [isaStepWith_sw profile s mem w rs1 rs2 imm hdecode]
  rfl

/- Every profile takes one non-trapping ISA step for a decoded 32-bit LW. -/
theorem isaStepWith_lw (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (rd rs1 : Reg) (imm : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.mem (.load true) .word rd rs1 imm)) :
    isaStepWith profile s mem (.word w) 0 =
      (lwNext s mem rd rs1 imm, lwEffects s rs1 imm) := by
  have hirq : takeInterrupt? s.csrs 0 = none := by
    simp [takeInterrupt?, pendingSet, selectIrq, irqPriority]
  simp only [isaStepWith, hirq, hdecode]
  simp [lwNext, lwEffects, execInstr, Fetched.size]

/- The memory-threaded LW reads the supplied memory and leaves it unchanged. -/
theorem isaStepMemWith_lw (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (rd rs1 : Reg) (imm : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.mem (.load true) .word rd rs1 imm)) :
    isaStepMemWith profile s mem (.word w) 0 =
      (lwNext s mem rd rs1 imm, mem) := by
  unfold isaStepMemWith
  rw [isaStepWith_lw profile s mem w rd rs1 imm hdecode]
  rfl

/- The generic machine adapter exposes the same LW commit boundary. -/
theorem rvMachineWith_lw (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (rd rs1 : Reg) (imm : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.mem (.load true) .word rd rs1 imm)) :
    (rvMachineWith profile).step s
        { fetched := .word w, memory := mem, irq := 0 } =
      (lwNext s mem rd rs1 imm, lwRetirement s
        { fetched := .word w, memory := mem, irq := 0 } rd rs1 imm) := by
  simp only [rvMachineWith]
  rw [isaStepWith_lw profile s mem w rd rs1 imm hdecode]
  rfl

#print axioms LeanModels.Refine.swNext_preserves_regs
#print axioms LeanModels.Refine.isaStepWith_sw
#print axioms LeanModels.Refine.isaStepMemWith_sw
#print axioms LeanModels.Refine.rvMachineWith_sw
#print axioms LeanModels.Refine.isaStepWith_lw
#print axioms LeanModels.Refine.isaStepMemWith_lw
#print axioms LeanModels.Refine.rvMachineWith_lw

end LeanModels.Refine
