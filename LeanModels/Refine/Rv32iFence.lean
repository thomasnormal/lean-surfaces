import LeanModels.Refine.Commit

/-!
# RV32I fence retirement boundary

`fence` and `fence.i` are both sequential, no-register, no-memory RV32I
system operations in the architectural model.  The operation stays explicit
through `FenceKind` so a core proof can retain the decoded system effect while
sharing the common pc and retirement equations.
-/

namespace LeanModels.Refine

open LeanModels.Rv

/-! ## Fence operation shape -/

/-- The two non-trapping fence operations in the RV32I/Zifencei subset. -/
inductive FenceKind where
  | fence
  | fenceI
  deriving DecidableEq, Repr

/-- The corresponding ISA system operation. -/
def FenceKind.toSysOp : FenceKind → SysOp
  | .fence => .fence
  | .fenceI => .fenceI

/-- The architectural state reached by one 32-bit fence operation. -/
def fenceNext (s : ArchState) (_kind : FenceKind) : ArchState :=
  { s with pc := s.pc + 4 }

/-- The architectural effects of one 32-bit fence operation. -/
def fenceEffects (s : ArchState) (kind : FenceKind) : StepEffects :=
  { pcTarget := s.pc + 4, sys := some kind.toSysOp }

/-- The exact ISA-side boundary contract for a fence parcel. -/
def fenceRetirement (s : ArchState) (input : Input) (kind : FenceKind) : Retirement :=
  Retirement.ofRvStep s input (fenceNext s kind) (fenceEffects s kind)

/-- Every profile takes one non-trapping ISA step for either fence operation
when interrupts are absent. -/
theorem isaStepWith_fence (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (kind : FenceKind)
    (hdecode : Fetched.decode (.word w) =
      some (.system kind.toSysOp)) :
    isaStepWith profile s mem (.word w) 0 =
      (fenceNext s kind, fenceEffects s kind) := by
  have hirq : takeInterrupt? s.csrs 0 = none := by
    simp [takeInterrupt?, pendingSet, selectIrq, irqPriority]
  simp only [isaStepWith, hirq, hdecode]
  cases kind <;> simp [FenceKind.toSysOp, SysOp.isEscape, fenceNext, fenceEffects,
    execInstr, Fetched.size]

/- The fence contract with architectural memory threaded through the
one-instruction driver: fences preserve memory exactly. -/
theorem isaStepMemWith_fence (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (kind : FenceKind)
    (hdecode : Fetched.decode (.word w) =
      some (.system kind.toSysOp)) :
    isaStepMemWith profile s mem (.word w) 0 =
      (fenceNext s kind, mem) := by
  unfold isaStepMemWith
  rw [isaStepWith_fence profile s mem w kind hdecode]
  rfl

/-- The generic machine adapter exposes the same fence commit boundary. -/
theorem rvMachineWith_fence (profile : PlatformProfile) (s : ArchState)
    (mem : Memory) (w : Word) (kind : FenceKind)
    (hdecode : Fetched.decode (.word w) =
      some (.system kind.toSysOp)) :
    (rvMachineWith profile).step s
        { fetched := .word w, memory := mem, irq := 0 } =
      (fenceNext s kind,
        fenceRetirement s { fetched := .word w, memory := mem, irq := 0 }
          kind) := by
  simp only [rvMachineWith]
  rw [isaStepWith_fence profile s mem w kind hdecode]
  rfl

#print axioms LeanModels.Refine.isaStepWith_fence
#print axioms LeanModels.Refine.isaStepMemWith_fence
#print axioms LeanModels.Refine.rvMachineWith_fence

end LeanModels.Refine
