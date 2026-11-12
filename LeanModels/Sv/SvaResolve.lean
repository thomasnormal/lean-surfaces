import LeanModels.Sv.Sva
import LeanModels.Sv.Kernel.XResolve

/-!
# X-E bridge at the SVA sampled-value boundary

SVA consumes sampled four-state values.  This module gives the first bridge
from an independent `XRead` witness to that retained evaluator: a known
sampled signal has the same boolean observation after per-read resolution.
The SVA evaluator and the E semantics remain unchanged.
-/

namespace LeanModels.Sv

open LeanModels.Sv.Kernel

theorem SvaBool.signal_evalLogic_xread {trace : List SvState} {index : Nat}
    {name : String} {source concrete : LVec}
    (hs : signalAt trace index name = .ok (some source))
    (hknown : source.bits.toList.all Logic.isKnown = true)
    (hread : XRead source concrete) :
    SvaBool.evalLogic trace index (.signal name) =
      .ok (some (boolLogic concrete)) := by
  simp only [SvaBool.evalLogic, hs]
  have heq := xRead_eq_of_known hknown hread
  cases heq
  rfl

end LeanModels.Sv

#print axioms LeanModels.Sv.SvaBool.signal_evalLogic_xread
