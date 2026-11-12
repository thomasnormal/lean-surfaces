import LeanModels.Sv.Kernel.MemE
import LeanModels.Sv.Kernel.XResolve

/-!
# X-E bridge at the MemE decision boundary

MemE remains a source-shaped derived profile.  This module gives it the first
known-read bridge without changing its evaluator: an `if` that consumed a
known `evalMemEExpr` result may be rewritten to the branch selected by that
read's independent `XRead` witness.  The full memory executor lift follows
the same pattern for case items and dynamic indices.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

theorem memE_if_xread {d : MemEDesign} {s : MemEState} {condition : PExpr}
    {concrete result : LVec} {α : Type} {thenBranch elseBranch : α}
    (heval : evalMemEExpr d s (some 1) condition = .ok result)
    (hknown : result.bits.toList.all Logic.isKnown = true)
    (hread : XRead result concrete) :
    (if result.condTrue then thenBranch else elseBranch) =
      (if concrete.condTrue then thenBranch else elseBranch) := by
  have heq := xRead_eq_of_known hknown hread
  cases heq
  rfl

end LeanModels.Sv.Kernel
