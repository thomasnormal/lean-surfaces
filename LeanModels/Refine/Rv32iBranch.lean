import LeanModels.Refine.Commit

/-!
# RV32I conditional-branch retirement boundaries

The six branch conditions share one architectural shape: compare two register
operands, choose either the signed/unsigned relative target or the sequential
pc, and write no registers or memory.  The condition remains an explicit
parameter so the refinement boundary covers the complete decoded branch
family without replacing the ISA operation by a collection of special cases.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-- The target selected by one 32-bit RV32I conditional branch. -/
def branchTarget (s : ArchState) (cond : BranchCond)
    (rs1 rs2 : Reg) (offset : Word) : Word :=
  if branchSem cond (s.readReg rs1) (s.readReg rs2) then
    s.pc + offset
  else s.pc + 4

/-- The architectural state reached by one 32-bit RV32I conditional branch. -/
def branchNext (s : ArchState) (cond : BranchCond)
    (rs1 rs2 : Reg) (offset : Word) : ArchState :=
  { s with pc := branchTarget s cond rs1 rs2 offset }

/-- The architectural effects of one 32-bit RV32I conditional branch. -/
def branchEffects (s : ArchState) (cond : BranchCond)
    (rs1 rs2 : Reg) (offset : Word) : StepEffects :=
  { pcTarget := branchTarget s cond rs1 rs2 offset }

/-- The exact ISA-side boundary contract for a conditional-branch parcel. -/
def branchRetirement (s : ArchState) (input : Input)
    (cond : BranchCond) (rs1 rs2 : Reg) (offset : Word) : Retirement :=
  Retirement.ofRvStep s input (branchNext s cond rs1 rs2 offset)
    (branchEffects s cond rs1 rs2 offset)

/-- Every profile takes one non-trapping ISA step for a conditional branch when
interrupts are absent. -/
theorem isaStepWith_branch (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (cond : BranchCond) (rs1 rs2 : Reg)
    (offset : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.branch cond rs1 rs2 offset)) :
    isaStepWith profile s mem (.word w) 0 =
      (branchNext s cond rs1 rs2 offset,
        branchEffects s cond rs1 rs2 offset) := by
  have hirq : takeInterrupt? s.csrs 0 = none := by
    simp [takeInterrupt?, pendingSet, selectIrq, irqPriority]
  simp only [isaStepWith, hirq, hdecode]
  simp [branchNext, branchEffects, branchTarget, execInstr, Fetched.size]

/- The branch contract with architectural memory threaded through the
one-instruction driver: branches preserve memory exactly. -/
theorem isaStepMemWith_branch (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (cond : BranchCond) (rs1 rs2 : Reg)
    (offset : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.branch cond rs1 rs2 offset)) :
    isaStepMemWith profile s mem (.word w) 0 =
      (branchNext s cond rs1 rs2 offset, mem) := by
  unfold isaStepMemWith
  rw [isaStepWith_branch profile s mem w cond rs1 rs2 offset hdecode]
  rfl

/-- The generic machine adapter exposes the same branch commit boundary. -/
theorem rvMachineWith_branch (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (cond : BranchCond) (rs1 rs2 : Reg)
    (offset : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.branch cond rs1 rs2 offset)) :
    (rvMachineWith profile).step s
        { fetched := .word w, memory := mem, irq := 0 } =
      (branchNext s cond rs1 rs2 offset,
        branchRetirement s { fetched := .word w, memory := mem, irq := 0 }
          cond rs1 rs2 offset) := by
  simp only [rvMachineWith]
  rw [isaStepWith_branch profile s mem w cond rs1 rs2 offset hdecode]
  rfl

#print axioms LeanModels.Refine.isaStepWith_branch
#print axioms LeanModels.Refine.isaStepMemWith_branch
#print axioms LeanModels.Refine.rvMachineWith_branch

end LeanModels.Refine
