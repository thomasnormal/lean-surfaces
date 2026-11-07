import LeanModels.Refine.Commit

/-!
# RV32I upper-immediate retirement boundaries

LUI uses the existing ALU decode family with `x0` as its first source and the
U-immediate as its second source.  The x0 read stays explicit in these
equations: callers may separately use the architectural `WF` invariant to
rewrite it to zero.  AUIPC uses the same family with the current pc as its
first source.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-- The architectural state reached by one 32-bit RV32I LUI. -/
def luiNext (s : ArchState) (rd : Reg) (imm : Word) : ArchState :=
  { s.writeReg rd (s.readReg 0 + imm) with pc := s.pc + 4 }

/-- The architectural effects of one 32-bit RV32I LUI. -/
def luiEffects (s : ArchState) : StepEffects :=
  { pcTarget := s.pc + 4 }

/-- The exact ISA-side boundary contract for an LUI parcel. -/
def luiRetirement (s : ArchState) (input : Input)
    (rd : Reg) (imm : Word) : Retirement :=
  Retirement.ofRvStep s input (luiNext s rd imm) (luiEffects s)

/- Every profile takes one non-trapping ISA step for an LUI when interrupts are
absent. -/
theorem isaStepWith_lui (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (rd : Reg) (imm : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.alu .add rd (.reg 0) (.imm imm))) :
    isaStepWith profile s mem (.word w) 0 =
      (luiNext s rd imm, luiEffects s) := by
  have hirq : takeInterrupt? s.csrs 0 = none := by
    simp [takeInterrupt?, pendingSet, selectIrq, irqPriority]
  simp only [isaStepWith, hirq, hdecode]
  simp [luiNext, luiEffects, execInstr, src1Val, src2Val, aluSem,
    Fetched.size]

/- The LUI contract with architectural memory threaded through the
one-instruction driver: LUI preserves memory exactly. -/
theorem isaStepMemWith_lui (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (rd : Reg) (imm : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.alu .add rd (.reg 0) (.imm imm))) :
    isaStepMemWith profile s mem (.word w) 0 =
      (luiNext s rd imm, mem) := by
  unfold isaStepMemWith
  rw [isaStepWith_lui profile s mem w rd imm hdecode]
  rfl

/-- The generic machine adapter exposes the same LUI commit boundary. -/
theorem rvMachineWith_lui (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (rd : Reg) (imm : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.alu .add rd (.reg 0) (.imm imm))) :
    (rvMachineWith profile).step s
        { fetched := .word w, memory := mem, irq := 0 } =
      (luiNext s rd imm,
        luiRetirement s { fetched := .word w, memory := mem, irq := 0 }
          rd imm) := by
  simp only [rvMachineWith]
  rw [isaStepWith_lui profile s mem w rd imm hdecode]
  rfl

#print axioms LeanModels.Refine.isaStepWith_lui
#print axioms LeanModels.Refine.isaStepMemWith_lui
#print axioms LeanModels.Refine.rvMachineWith_lui

/-! ## AUIPC -/

/-- The architectural state reached by one 32-bit RV32I AUIPC. -/
def auipcNext (s : ArchState) (rd : Reg) (imm : Word) : ArchState :=
  { s.writeReg rd (s.pc + imm) with pc := s.pc + 4 }

/-- The architectural effects of one 32-bit RV32I AUIPC. -/
def auipcEffects (s : ArchState) : StepEffects :=
  { pcTarget := s.pc + 4 }

/-- The exact ISA-side boundary contract for an AUIPC parcel. -/
def auipcRetirement (s : ArchState) (input : Input)
    (rd : Reg) (imm : Word) : Retirement :=
  Retirement.ofRvStep s input (auipcNext s rd imm) (auipcEffects s)

/- Every profile takes one non-trapping ISA step for AUIPC when interrupts are
absent. -/
theorem isaStepWith_auipc (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (rd : Reg) (imm : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.alu .add rd .pc (.imm imm))) :
    isaStepWith profile s mem (.word w) 0 =
      (auipcNext s rd imm, auipcEffects s) := by
  have hirq : takeInterrupt? s.csrs 0 = none := by
    simp [takeInterrupt?, pendingSet, selectIrq, irqPriority]
  simp only [isaStepWith, hirq, hdecode]
  simp [auipcNext, auipcEffects, execInstr, src1Val, src2Val, aluSem,
    Fetched.size]

/- The AUIPC contract with architectural memory threaded through the
one-instruction driver: AUIPC preserves memory exactly. -/
theorem isaStepMemWith_auipc (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (rd : Reg) (imm : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.alu .add rd .pc (.imm imm))) :
    isaStepMemWith profile s mem (.word w) 0 =
      (auipcNext s rd imm, mem) := by
  unfold isaStepMemWith
  rw [isaStepWith_auipc profile s mem w rd imm hdecode]
  rfl

/-- The generic machine adapter exposes the same AUIPC commit boundary. -/
theorem rvMachineWith_auipc (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (rd : Reg) (imm : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.alu .add rd .pc (.imm imm))) :
    (rvMachineWith profile).step s
        { fetched := .word w, memory := mem, irq := 0 } =
      (auipcNext s rd imm,
        auipcRetirement s { fetched := .word w, memory := mem, irq := 0 }
          rd imm) := by
  simp only [rvMachineWith]
  rw [isaStepWith_auipc profile s mem w rd imm hdecode]
  rfl

#print axioms LeanModels.Refine.isaStepWith_auipc
#print axioms LeanModels.Refine.isaStepMemWith_auipc
#print axioms LeanModels.Refine.rvMachineWith_auipc

end LeanModels.Refine
