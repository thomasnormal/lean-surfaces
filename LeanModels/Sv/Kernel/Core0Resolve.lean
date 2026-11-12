import LeanModels.Sv.Kernel.Core0Proc
import LeanModels.Sv.Kernel.XResolve

/-!
# Resolved decisions at the E combinational boundary

`Core0Proc.execBody` is the source-shaped always-comb evaluator.  This bridge
consumes the same `ResolvedDecision` witness as the edge route, so a
combinational conditional may be related to a concrete resolution without
promoting `condTrue`'s unknown branch to a proof rule.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

theorem execBody_if_resolved {E : Elab} {s : Store} {c : Expr2}
    {t : Stmt2} {e : Option Stmt2} {source result : LVec}
    (heval : evalPure2 (E.view s) c = .ok result)
    (hresolved : ResolvedDecision source result) :
    execBody E (.ifStmt c t e) s =
      (if source.condTrue then execBody E t else execBodyOpt E e) s := by
  rw [execBody_if_run heval]
  have hb := (hresolved.branch_eq (execBody E t s) (execBodyOpt E e s)).symm
  by_cases hr : result.condTrue = true <;> by_cases hs : source.condTrue = true <;>
    simpa [hr, hs] using hb

/-- Known-read refinement through the new independent X-E relation.  The
    evaluator remains the exact E evaluator; this theorem only exposes the
    branch chosen by a per-read witness under the known premise. -/
theorem execBody_if_xread {E : Elab} {s : Store} {c : Expr2}
    {t : Stmt2} {e : Option Stmt2} {concrete result : LVec}
    (heval : evalPure2 (E.view s) c = .ok result)
    (hknown : result.bits.toList.all Logic.isKnown = true)
    (hread : XRead result concrete) :
    execBody E (.ifStmt c t e) s =
      (if concrete.condTrue then execBody E t else execBodyOpt E e) s := by
  rw [execBody_if_run heval]
  have heq := xRead_eq_of_known hknown hread
  cases heq
  rfl

example {E : Elab} {s : Store} {c : Expr2} {t : Stmt2}
    {e : Option Stmt2} {result : LVec}
    (heval : evalPure2 (E.view s) c = .ok result)
    (hknown : result.bits.toList.all Logic.isKnown = true) :
    execBody E (.ifStmt c t e) s =
      (if result.condTrue then execBody E t else execBodyOpt E e) s := by
  exact execBody_if_resolved heval
    (ResolvedDecision.of_allKnown (source := result) (result := result)
      hknown (by rw [concretizations_of_known hknown]; simp))

end LeanModels.Sv.Kernel
