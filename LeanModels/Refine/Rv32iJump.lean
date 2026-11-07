import LeanModels.Refine.Commit

/-!
# RV32I jump retirement boundaries

JAL and JALR are one semantic family in the ISA model: both write the link
address and redirect the pc, with the base selecting either the current pc or a
register.  These equations keep the two decoded shapes separate at the
refinement boundary so a core proof cannot silently forget JALR's bit-zero
clearing rule.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## JAL -/

/-- The architectural state reached by one 32-bit RV32I JAL. -/
def jalNext (s : ArchState) (rd : Reg) (offset : Word) : ArchState :=
  { s.writeReg rd (s.pc + 4) with pc := s.pc + offset }

/-- The architectural effects of one 32-bit RV32I JAL. -/
def jalEffects (s : ArchState) (offset : Word) : StepEffects :=
  { pcTarget := s.pc + offset }

/-- The exact ISA-side boundary contract for a JAL parcel. -/
def jalRetirement (s : ArchState) (input : Input)
    (rd : Reg) (offset : Word) : Retirement :=
  Retirement.ofRvStep s input (jalNext s rd offset) (jalEffects s offset)

/-- Every profile takes one non-trapping ISA step for a JAL when interrupts are
absent. -/
theorem isaStepWith_jal (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (rd : Reg) (offset : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.jump rd .pc offset)) :
    isaStepWith profile s mem (.word w) 0 =
      (jalNext s rd offset, jalEffects s offset) := by
  have hirq : takeInterrupt? s.csrs 0 = none := by
    simp [takeInterrupt?, pendingSet, selectIrq, irqPriority]
  simp only [isaStepWith, hirq, hdecode]
  simp [jalNext, jalEffects, execInstr, jumpTarget, Fetched.size]

/- The JAL contract with architectural memory threaded through the
one-instruction driver: JAL preserves memory exactly. -/
theorem isaStepMemWith_jal (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (rd : Reg) (offset : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.jump rd .pc offset)) :
    isaStepMemWith profile s mem (.word w) 0 =
      (jalNext s rd offset, mem) := by
  unfold isaStepMemWith
  rw [isaStepWith_jal profile s mem w rd offset hdecode]
  rfl

/-- The generic machine adapter exposes the same JAL commit boundary. -/
theorem rvMachineWith_jal (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (rd : Reg) (offset : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.jump rd .pc offset)) :
    (rvMachineWith profile).step s
        { fetched := .word w, memory := mem, irq := 0 } =
      (jalNext s rd offset,
        jalRetirement s { fetched := .word w, memory := mem, irq := 0 }
          rd offset) := by
  simp only [rvMachineWith]
  rw [isaStepWith_jal profile s mem w rd offset hdecode]
  rfl

/-! ## JALR -/

/-- The target selected by one 32-bit RV32I JALR. -/
def jalrTarget (s : ArchState) (rs1 : Reg) (offset : Word) : Word :=
  jumpTarget s (.reg rs1) offset

/-- The architectural state reached by one 32-bit RV32I JALR. -/
def jalrNext (s : ArchState) (rd rs1 : Reg) (offset : Word) : ArchState :=
  { s.writeReg rd (s.pc + 4) with pc := jalrTarget s rs1 offset }

/-- The architectural effects of one 32-bit RV32I JALR. -/
def jalrEffects (s : ArchState) (rs1 : Reg) (offset : Word) : StepEffects :=
  { pcTarget := jalrTarget s rs1 offset }

/-- The exact ISA-side boundary contract for a JALR parcel. -/
def jalrRetirement (s : ArchState) (input : Input)
    (rd rs1 : Reg) (offset : Word) : Retirement :=
  Retirement.ofRvStep s input (jalrNext s rd rs1 offset)
    (jalrEffects s rs1 offset)

/-- Every profile takes one non-trapping ISA step for a JALR when interrupts are
absent. -/
theorem isaStepWith_jalr (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (rd rs1 : Reg) (offset : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.jump rd (.reg rs1) offset)) :
    isaStepWith profile s mem (.word w) 0 =
      (jalrNext s rd rs1 offset, jalrEffects s rs1 offset) := by
  have hirq : takeInterrupt? s.csrs 0 = none := by
    simp [takeInterrupt?, pendingSet, selectIrq, irqPriority]
  simp only [isaStepWith, hirq, hdecode]
  simp [jalrNext, jalrEffects, jalrTarget, execInstr, jumpTarget,
    Fetched.size]

/- The JALR contract with architectural memory threaded through the
one-instruction driver: JALR preserves memory exactly. -/
theorem isaStepMemWith_jalr (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (rd rs1 : Reg) (offset : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.jump rd (.reg rs1) offset)) :
    isaStepMemWith profile s mem (.word w) 0 =
      (jalrNext s rd rs1 offset, mem) := by
  unfold isaStepMemWith
  rw [isaStepWith_jalr profile s mem w rd rs1 offset hdecode]
  rfl

/-- The generic machine adapter exposes the same JALR commit boundary. -/
theorem rvMachineWith_jalr (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (rd rs1 : Reg) (offset : Word)
    (hdecode : Fetched.decode (.word w) =
      some (.jump rd (.reg rs1) offset)) :
    (rvMachineWith profile).step s
        { fetched := .word w, memory := mem, irq := 0 } =
      (jalrNext s rd rs1 offset,
        jalrRetirement s { fetched := .word w, memory := mem, irq := 0 }
          rd rs1 offset) := by
  simp only [rvMachineWith]
  rw [isaStepWith_jalr profile s mem w rd rs1 offset hdecode]
  rfl

#print axioms LeanModels.Refine.isaStepWith_jal
#print axioms LeanModels.Refine.isaStepMemWith_jal
#print axioms LeanModels.Refine.rvMachineWith_jal
#print axioms LeanModels.Refine.isaStepWith_jalr
#print axioms LeanModels.Refine.isaStepMemWith_jalr
#print axioms LeanModels.Refine.rvMachineWith_jalr

end LeanModels.Refine
