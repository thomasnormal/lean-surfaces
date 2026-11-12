import LeanModels.Sv.Kernel.Core1Edge
import LeanModels.Sv.Kernel.XResolve

/-!
# Resolved decisions at the E edge boundary

`Core1Edge.execFF` is the source-shaped edge evaluator.  This file gives its
first resolution-aware bridge: when an evaluated condition carries a
`ResolvedDecision`, the edge step can be related to the branch selected by
the concrete resolution.  The evaluator itself is unchanged; the witness is
the explicit proof boundary required before an unknown condition may be used
by a theorem.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

theorem execFF_if_resolved {d : Design2} {st : SvState} {c : Expr2}
    {t : Stmt2} {e : Option Stmt2} {source result : LVec}
    (heval : evalPure2 st c = .ok result)
    (hresolved : ResolvedDecision source result) :
    execFF d st (.ifStmt c t e) =
      (if source.condTrue then execFF d st t else execFFOpt d st e) := by
  simp only [execFF, heval]
  exact (hresolved.branch_eq (execFF d st t) (execFFOpt d st e)).symm

/-- Known-read refinement for the independent X-E relation at an edge body.
    `execFF` stays the exact source-shaped evaluator; this is only its
    proof-facing branch bridge. -/
theorem execFF_if_xread {d : Design2} {st : SvState} {c : Expr2}
    {t : Stmt2} {e : Option Stmt2} {concrete result : LVec}
    (heval : evalPure2 st c = .ok result)
    (hknown : result.bits.toList.all Logic.isKnown = true)
    (hread : XRead result concrete) :
    execFF d st (.ifStmt c t e) =
      (if concrete.condTrue then execFF d st t else execFFOpt d st e) := by
  simp only [execFF, heval]
  have heq := xRead_eq_of_known hknown hread
  cases heq
  rfl

/- A known condition is enough to construct the bridge's witness. -/
example {d : Design2} {st : SvState} {c : Expr2} {t : Stmt2}
    {e : Option Stmt2} {result : LVec}
    (heval : evalPure2 st c = .ok result)
    (hknown : result.bits.toList.all Logic.isKnown = true) :
    execFF d st (.ifStmt c t e) =
      (if result.condTrue then execFF d st t else execFFOpt d st e) := by
  exact execFF_if_resolved heval
    (ResolvedDecision.of_allKnown (source := result) (result := result)
      hknown (by rw [concretizations_of_known hknown]; simp))

end LeanModels.Sv.Kernel
