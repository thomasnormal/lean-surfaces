import LeanModels.Refine.Rv32iFence

/-!
# RV32I system-transfer retirement boundary

The non-CSR machine-mode system parcels used by the R2 subset share one
profile-parametric boundary.  ECALL and EBREAK enter the architectural trap
state, MRET returns through the CSR state, and WFI is the no-wake stutter when
the admitted input has no interrupt.  The system operation remains explicit
in `SysKind`, while the commit-level retirement is derived from the exact ISA
step.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## System operation shape -/

/-- Non-CSR machine-mode system operations in the no-interrupt R2 subset. -/
inductive SysKind where
  | ecall
  | ebreak
  | mret
  | wfi
  deriving DecidableEq, Repr

/-- The corresponding architectural system operation. -/
def SysKind.toSysOp : SysKind → SysOp
  | .ecall => .ecall
  | .ebreak => .ebreak
  | .mret => .mret
  | .wfi => .wfi

/-! ## Architectural system equations -/

/-- The architectural state after one admitted system operation. -/
def systemNext (s : ArchState) : SysKind → ArchState
  | .ecall => trapEnter s .ecallM
  | .ebreak => trapEnter s .breakpoint
  | .mret => mret s
  | .wfi => s

/-- The architectural effects after one admitted system operation. -/
def systemEffects (s : ArchState) : SysKind → StepEffects
  | .ecall =>
      { pcTarget := (trapEnter s .ecallM).pc
        sys := some .ecall
        trap := some .ecallM }
  | .ebreak =>
      { pcTarget := (trapEnter s .breakpoint).pc
        sys := some .ebreak
        trap := some .breakpoint }
  | .mret =>
      { pcTarget := (mret s).pc, sys := some .mret }
  | .wfi =>
      { pcTarget := s.pc, sys := some .wfi }

/-- The exact ISA-side retirement for an admitted system parcel. -/
def systemRetirement (s : ArchState) (input : Input) (kind : SysKind) : Retirement :=
  Retirement.ofRvStep s input (systemNext s kind) (systemEffects s kind)

/-- Every profile takes the exact non-interrupt system step when the fetched
parcel decodes to the selected operation. -/
theorem isaStepWith_system (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (kind : SysKind)
    (hdecode : Fetched.decode (.word w) =
      some (.system kind.toSysOp)) :
    isaStepWith profile s mem (.word w) 0 =
      (systemNext s kind, systemEffects s kind) := by
  have hirq : takeInterrupt? s.csrs 0 = none := by
    simp [takeInterrupt?, pendingSet, selectIrq, irqPriority]
  simp only [isaStepWith, hirq, hdecode]
  cases kind <;>
    simp [SysKind.toSysOp, systemNext, systemEffects, wfiWake,
      pendingSet, mstatusOnTrap, trapEnter, trapVector, mret]

/-- System operations do not alter the threaded data memory. -/
theorem isaStepMemWith_system (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (kind : SysKind)
    (hdecode : Fetched.decode (.word w) =
      some (.system kind.toSysOp)) :
    isaStepMemWith profile s mem (.word w) 0 =
      (systemNext s kind, mem) := by
  unfold isaStepMemWith
  rw [isaStepWith_system profile s mem w kind hdecode]
  cases kind <;> rfl

/-- The generic machine adapter exposes the same system commit boundary. -/
theorem rvMachineWith_system (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (kind : SysKind)
    (hdecode : Fetched.decode (.word w) =
      some (.system kind.toSysOp)) :
    (rvMachineWith profile).step s
        { fetched := .word w, memory := mem, irq := 0 } =
      (systemNext s kind,
        systemRetirement s { fetched := .word w, memory := mem, irq := 0 }
          kind) := by
  simp only [rvMachineWith]
  rw [isaStepWith_system profile s mem w kind hdecode]
  rfl

#print axioms LeanModels.Refine.isaStepWith_system
#print axioms LeanModels.Refine.isaStepMemWith_system
#print axioms LeanModels.Refine.rvMachineWith_system

end LeanModels.Refine
