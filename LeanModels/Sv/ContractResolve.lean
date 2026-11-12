import LeanModels.Sv.Contract
import LeanModels.Sv.Kernel.XResolve

/-!
# X-E bridge for contract input valuations

Contract relies and guarantees are stated over trusted port samples.  This
lemma records the known-value case needed by that boundary: an independent
X-E read of a known valuation cannot change `HoldsOn`.  No contract meaning
or observation evaluator is changed.
-/

namespace LeanModels.Sv.Observe

open LeanModels.Sv.Kernel

theorem HoldsOn.of_xread {s s' : PortSample} {sigs : List Sig} {v : Valuation}
    (h : HoldsOn s sigs v)
    (hread : ∀ p, p ∈ sigs → ∃ source concrete,
      s.read p.1 = some source ∧ s'.read p.1 = some concrete ∧ XRead source concrete) :
    HoldsOn s' sigs v := by
  intro p hp
  obtain ⟨source, concrete, hsource, hconcrete, hx⟩ := hread p hp
  have hsource' : source = LVec.ofBitVec (v p) :=
    Option.some.inj (hsource.symm.trans (h p hp))
  cases hsource'
  rw [hconcrete]
  have hknown : (LVec.ofBitVec (v p)).bits.toList.all Logic.isKnown = true := by
    simp [LVec.ofBitVec, LVec.ofNat, LVec.allKnown,
      Array.all_eq_true_iff_forall_mem, Array.mem_ofFn, Logic.isKnown]
    intro i
    by_cases hb : (v p).toNat.testBit (i : Nat) = true <;> simp [hb]
  have heq := xRead_eq_of_known hknown hx
  cases heq
  exact rfl

end LeanModels.Sv.Observe

#print axioms LeanModels.Sv.Observe.HoldsOn.of_xread
