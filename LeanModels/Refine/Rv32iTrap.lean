import LeanModels.Refine.Rv32iCsr

/-!
# RV32I illegal-instruction retirement boundary

An undecodable 32-bit parcel enters the machine-mode illegal-instruction trap.
This boundary keeps the handler pc and precise cause explicit; it does not
reuse a no-op system boundary and therefore cannot turn malformed input into a
retired sequential instruction.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-- The architectural state after an undecodable 32-bit parcel. -/
def illegalNext (s : ArchState) : ArchState :=
  trapEnter s .illegalInstr

/-- The architectural effects after an undecodable 32-bit parcel. -/
def illegalEffects (s : ArchState) : StepEffects :=
  { pcTarget := (illegalNext s).pc
    trap := some .illegalInstr }

/-- The exact ISA-side retirement for an undecodable 32-bit parcel. -/
def illegalRetirement (s : ArchState) (input : Input) : Retirement :=
  Retirement.ofRvStep s input (illegalNext s) (illegalEffects s)

/-- Every profile enters the illegal-instruction trap for a decode failure when
interrupts are absent. -/
theorem isaStepWith_illegal (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word)
    (hdecode : Fetched.decode (.word w) = none) :
    isaStepWith profile s mem (.word w) 0 =
      (illegalNext s, illegalEffects s) := by
  have hirq : takeInterrupt? s.csrs 0 = none := by
    simp [takeInterrupt?, pendingSet, selectIrq, irqPriority]
  simp only [isaStepWith, hirq, hdecode]
  rfl

/-- An illegal instruction does not apply a data-memory effect. -/
theorem isaStepMemWith_illegal (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word)
    (hdecode : Fetched.decode (.word w) = none) :
    isaStepMemWith profile s mem (.word w) 0 =
      (illegalNext s, mem) := by
  unfold isaStepMemWith
  rw [isaStepWith_illegal profile s mem w hdecode]
  rfl

/-- The generic machine adapter exposes the illegal-instruction boundary. -/
theorem rvMachineWith_illegal (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word)
    (hdecode : Fetched.decode (.word w) = none) :
    (rvMachineWith profile).step s
        { fetched := .word w, memory := mem, irq := 0 } =
      (illegalNext s, illegalRetirement s
        { fetched := .word w, memory := mem, irq := 0 }) := by
  simp only [rvMachineWith]
  rw [isaStepWith_illegal profile s mem w hdecode]
  rfl

#print axioms LeanModels.Refine.isaStepWith_illegal
#print axioms LeanModels.Refine.isaStepMemWith_illegal
#print axioms LeanModels.Refine.rvMachineWith_illegal

/-! ## Unimplemented CSR trap -/

/-- An implemented CSR row is required for the Zicsr step; an absent row
enters the same illegal-instruction trap as a decode failure. -/
theorem isaStepWith_illegal_csr (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (kind : CsrOpKind)
    (hdecode : Fetched.decode (.word w) = some kind.toInstr)
    (hrow : findCsr? kind.addr = none) :
    isaStepWith profile s mem (.word w) 0 =
      (illegalNext s, illegalEffects s) := by
  cases kind with
  | mk op rd src addr =>
    change Fetched.decode (.word w) =
      some (.system (.csr op rd src addr)) at hdecode
    change findCsr? addr = none at hrow
    have hirq : takeInterrupt? s.csrs 0 = none := by
      simp [takeInterrupt?, pendingSet, selectIrq, irqPriority]
    simp only [isaStepWith, hirq, hdecode]
    rw [hrow]
    rfl

theorem isaStepMemWith_illegal_csr (profile : PlatformProfile)
    (s : ArchState) (mem : Memory) (w : Word) (kind : CsrOpKind)
    (hdecode : Fetched.decode (.word w) = some kind.toInstr)
    (hrow : findCsr? kind.addr = none) :
    isaStepMemWith profile s mem (.word w) 0 =
      (illegalNext s, mem) := by
  unfold isaStepMemWith
  rw [isaStepWith_illegal_csr profile s mem w kind hdecode hrow]
  rfl

theorem rvMachineWith_illegal_csr (profile : PlatformProfile)
    (s : ArchState) (mem : Memory) (w : Word) (kind : CsrOpKind)
    (hdecode : Fetched.decode (.word w) = some kind.toInstr)
    (hrow : findCsr? kind.addr = none) :
    (rvMachineWith profile).step s
        { fetched := .word w, memory := mem, irq := 0 } =
      (illegalNext s, illegalRetirement s
        { fetched := .word w, memory := mem, irq := 0 }) := by
  simp only [rvMachineWith]
  rw [isaStepWith_illegal_csr profile s mem w kind hdecode hrow]
  rfl

#print axioms LeanModels.Refine.isaStepWith_illegal_csr
#print axioms LeanModels.Refine.isaStepMemWith_illegal_csr
#print axioms LeanModels.Refine.rvMachineWith_illegal_csr

end LeanModels.Refine
