import LeanModels.Sv.ObserveE
import LeanModels.Sv.Kernel.XResolve

/-!
# X-E bridge at the trusted observation boundary

The observation model restricts backend probes to declared ports.  This module
proves that a known port read keeps its value when an independent X-E witness
is applied before the port projection.  Sampling itself and E remain
unchanged.
-/

namespace LeanModels.Sv.Observe

open LeanModels.Sv
open LeanModels.Sv.Kernel

theorem ObservationModel.sample_read_xread (M : ObservationModel)
    {d : M.Design} {p : M.Probe} {name : String} {source concrete : LVec}
    (hport : name ∈ (M.iface d).names)
    (hread : M.read p name = some source)
    (hknown : source.bits.toList.all Logic.isKnown = true)
    (hx : XRead source concrete) :
    (M.sample d p).read name = some concrete := by
  rw [ObservationModel.read_sample]
  simp [hport, hread]
  have heq := xRead_eq_of_known hknown hx
  cases heq
  rfl

end LeanModels.Sv.Observe

#print axioms LeanModels.Sv.Observe.ObservationModel.sample_read_xread
