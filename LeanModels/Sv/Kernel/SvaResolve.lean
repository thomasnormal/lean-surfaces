import LeanModels.Sv.Sva
import LeanModels.Sv.Kernel.XResolve

/-!
# X-E bridge for sampled SVA values

This first SVA bridge lifts the known-read refinement through the assertion
case-equality observer. It does not change SVA evaluation or choose a value for
an unknown; unknown samples remain outside this theorem's known-read premise.
-/
namespace LeanModels.Sv.Kernel
open LeanModels.Sv

 theorem sva_caseEqual_xread_left {a a' b : LVec}
    (hknown : a.bits.toList.all Logic.isKnown = true)
    (hread : XRead a a') :
    caseEqual (some a) (some b) = caseEqual (some a') (some b) := by
  have h := xRead_eq_of_known hknown hread
  cases h
  rfl

theorem sva_caseEqual_xread_right {a b b' : LVec}
    (hknown : b.bits.toList.all Logic.isKnown = true)
    (hread : XRead b b') :
    caseEqual (some a) (some b) = caseEqual (some a) (some b') := by
  have h := xRead_eq_of_known hknown hread
  cases h
  rfl

end LeanModels.Sv.Kernel
