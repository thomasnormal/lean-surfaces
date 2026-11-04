import Examples.«system-verilog».comb_multi.gen
import LeanModels.Sv.CombProcTactic

/-!
# A body that writes TWO windows, proved (WP-G S1b, gate d)

`multi_flat.sv` writes `y = a; if (e) y = b;` and then `z = a ^ b;` in ONE `always_comb`. `sv_equations` states one
equation and one knownness fact per window: the head window's under the names of the single-window route
(`eq_y_plain_0`), the second window's with `_w1` (`eq_z_plain_0_w1`), and the stable aliases `eq_y_1`, `eq_z_1` count
the WINDOWS that write each signal, exactly as they count the assigns that write it (`comb_hint.lean`).

* `multi_same_settles`: two windows of ONE signal in one body (`y[0]`, `y[1]`).
* `multi_flat_settles`: in every settled state of the lowered design whose `a`, `b`, `e` are known, `y` is
  `if e then b else a` and `z` is `a ^^^ b`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».comb_multi.gen

namespace Examples.«system-verilog».comb_multi.comb_proof

/-- **The two-window body, proved**: both windows of the one `always_comb`. -/
theorem multi_flat_settles {d' : Design2} (_hl : multi_flat.sem.lowerComb = some d') (_hc : CombDesign d')
    (_ha : Acyclic d') (st : SvState) (_heqs : CombEqs d' st) (_hsh : StateShape d' st)
    (a b : BitVec 4) (e : BitVec 1)
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec a))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec b))
    (hE : SvState.lookup st "e" = some (LVec.ofBitVec e)) :
    SvState.lookup st "y" = some (LVec.ofBitVec (if e.getLsbD 0 then b else a)) ∧
    SvState.lookup st "z" = some (LVec.ofBitVec (a ^^^ b)) := by
  sv_equations
  · have ba : ∀ j, j < 4 → st.boolAt "a" j = a.getLsbD j := fun j hj => SvState.boolAt_ofBitVec hA hj
    have bb : ∀ j, j < 4 → st.boolAt "b" j = b.getLsbD j := fun j hj => SvState.boolAt_ofBitVec hB hj
    have be : st.boolAt "e" 0 = e.getLsbD 0 := SvState.boolAt_ofBitVec hE (by omega)
    refine ⟨?_, ?_⟩
    · obtain ⟨⟨vs, hvs, hvsw⟩, -⟩ := known_y_1 0 (by simp)
      have hks : ∀ k, k < 4 → KnownBit st "y" k := fun k hk => (known_y_1 k (by simp; omega)).2
      have hvy := SvState.lookup_eq_ofBitVec_bv hvs (by simpa using hvsw) hks
      rw [hvy] at hvs
      rw [hvs]
      have h : XF.bv 4 (st.boolAt "y") = if e.getLsbD 0 then b else a := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        rw [XF.getLsbD_bv hi, eq_y_1 i (by simp; omega), ba i hi, bb i hi, be]
        cases e.getLsbD 0 <;> simp
      rw [h]
    · obtain ⟨⟨vs, hvs, hvsw⟩, -⟩ := known_z_1 0 (by simp)
      have hks : ∀ k, k < 4 → KnownBit st "z" k := fun k hk => (known_z_1 k (by simp; omega)).2
      have hvz := SvState.lookup_eq_ofBitVec_bv hvs (by simpa using hvsw) hks
      rw [hvz] at hvs
      rw [hvs]
      have h : XF.bv 4 (st.boolAt "z") = a ^^^ b := by
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        rw [XF.getLsbD_bv hi, eq_z_1 i (by simp; omega), ba i hi, bb i hi]
        simp
      rw [h]
  all_goals first
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hE ?_; omega)

/-- info: 'Examples.«system-verilog».comb_multi.comb_proof.multi_flat_settles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms multi_flat_settles

/-- **Two windows of one signal, proved**: `y[0]` and `y[1]` of one body, the aliases `eq_y_1`, `eq_y_2` and
`known_y_1`, `known_y_2` (the ordinals count windows in source order). -/
theorem multi_same_settles {d' : Design2} (_hl : multi_same.sem.lowerComb = some d') (_hc : CombDesign d')
    (_ha : Acyclic d') (st : SvState) (_heqs : CombEqs d' st) (_hsh : StateShape d' st)
    (a b : BitVec 2)
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec a))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec b)) :
    ∃ y : BitVec 2, SvState.lookup st "y" = some (LVec.ofBitVec y) ∧
      y.getLsbD 0 = (a.getLsbD 0 && b.getLsbD 0) ∧ y.getLsbD 1 = (a.getLsbD 1 || b.getLsbD 1) := by
  sv_equations
  · have ba : ∀ j, j < 2 → st.boolAt "a" j = a.getLsbD j := fun j hj => SvState.boolAt_ofBitVec hA hj
    have bb : ∀ j, j < 2 → st.boolAt "b" j = b.getLsbD j := fun j hj => SvState.boolAt_ofBitVec hB hj
    obtain ⟨⟨v, hv, hvw⟩, k0⟩ := known_y_1
    obtain ⟨-, k1⟩ := known_y_2
    have hks : ∀ k, k < 2 → KnownBit st "y" k := by
      intro k hk
      obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
      · exact k0
      · exact k1
    have hvy := SvState.lookup_eq_ofBitVec_bv hv (by simpa using hvw) hks
    rw [hvy] at hv
    refine ⟨XF.bv 2 (st.boolAt "y"), hv, ?_, ?_⟩
    · rw [XF.getLsbD_bv (show 0 < 2 by omega), eq_y_1, ba 0 (by omega), bb 0 (by omega)]
    · have e2 : st.boolAt "y" 1 = (a.getLsbD 1 || b.getLsbD 1) := by
        have h2 := eq_y_2
        first
          | (simp only [show Int.toNat 1 = 1 from rfl, ba 1 (by omega), bb 1 (by omega)] at h2; exact h2)
          | simpa [show Int.toNat 1 = 1 from rfl, ba 1 (by omega), bb 1 (by omega)] using h2
      rw [XF.getLsbD_bv (show 1 < 2 by omega), e2]
  all_goals first
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)

/-- info: 'Examples.«system-verilog».comb_multi.comb_proof.multi_same_settles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms multi_same_settles

end Examples.«system-verilog».comb_multi.comb_proof
