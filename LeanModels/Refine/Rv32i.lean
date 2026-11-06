import LeanModels.Refine.Commit

/-!
# RV32I ADDI retirement boundary

This file is the first architectural contract for the PicoRV32 R2 proof.  It
is deliberately independent of any core state: a loaded core invariant will
show that its ADDI retirement agrees with these exact ISA equations.  The
contract does not assume `RobStepRefines` or any finite witness.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-- The architectural state reached by one 32-bit RV32I ADDI. -/
def addiNext (s : ArchState) (rd rs1 : Reg) (imm : Word) : ArchState :=
  { s.writeReg rd (s.readReg rs1 + imm) with pc := s.pc + 4 }

/-- The architectural effects of one 32-bit RV32I ADDI. -/
def addiEffects (s : ArchState) : StepEffects :=
  { pcTarget := s.pc + 4 }

/-- The exact ISA-side boundary contract for an ADDI parcel. -/
def addiRetirement (s : ArchState) (input : Input)
    (rd rs1 : Reg) (imm : Word) : Retirement :=
  Retirement.ofRvStep s input (addiNext s rd rs1 imm) (addiEffects s)

/-- Every profile takes one non-trapping ISA step for an ADDI when interrupts
are absent.  The decoder hypothesis is deliberately on the parsed `Fetched`
value; a core proof supplies it from the actual instruction word. -/
theorem isaStepWith_addi (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (rd rs1 : Reg) (imm : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.alu .add rd (.reg rs1) (.imm imm))) :
    isaStepWith profile s mem (.word w) 0 =
      (addiNext s rd rs1 imm, addiEffects s) := by
  have hirq : takeInterrupt? s.csrs 0 = none := by
    simp [takeInterrupt?, pendingSet, selectIrq, irqPriority]
  simp only [isaStepWith, hirq, hdecode]
  simp [addiNext, addiEffects, execInstr, src1Val, src2Val, aluSem,
    Fetched.size]

/-- The ADDI contract with the architectural memory threaded through the
one-instruction driver: ADDI preserves memory exactly. -/
theorem isaStepMemWith_addi (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (rd rs1 : Reg) (imm : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.alu .add rd (.reg rs1) (.imm imm))) :
    isaStepMemWith profile s mem (.word w) 0 =
      (addiNext s rd rs1 imm, mem) := by
  unfold isaStepMemWith
  rw [isaStepWith_addi profile s mem w rd rs1 imm hdecode]
  rfl

/-- The generic machine adapter exposes the same ADDI commit boundary. -/
theorem rvMachineWith_addi (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (rd rs1 : Reg) (imm : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.alu .add rd (.reg rs1) (.imm imm))) :
    (rvMachineWith profile).step s
        { fetched := .word w, memory := mem, irq := 0 } =
      (addiNext s rd rs1 imm,
        addiRetirement s { fetched := .word w, memory := mem, irq := 0 }
          rd rs1 imm) := by
  simp only [rvMachineWith]
  rw [isaStepWith_addi profile s mem w rd rs1 imm hdecode]
  rfl

#print axioms LeanModels.Refine.isaStepWith_addi
#print axioms LeanModels.Refine.isaStepMemWith_addi
#print axioms LeanModels.Refine.rvMachineWith_addi

end LeanModels.Refine
