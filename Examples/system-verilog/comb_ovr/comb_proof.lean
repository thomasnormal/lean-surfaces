import Examples.«system-verilog».comb_ovr.gen
import LeanModels.Sv.CombProcTactic

/-!
# A priority encoder as default-then-override, proved (WP-G S3b)

`prio_enc.sv` writes `y = 2'd0;` and then three overrides, `if (r[1]) y = 2'd1;`, `if (r[2]) y = 2'd2;`,
`if (r[3]) y = 2'd3;`: the last write wins, so the highest requesting line gives its index. `sv_equations` states
the one equation of `y` as the nested choice, the LAST override outermost (`comb_hint.lean`), and the proof is a
case split on the three request bits.

* `prio`: the function the design computes;
* `prio_settles`: in every settled state of the lowered design whose `r` is `r`, `y` is `prio r`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».comb_ovr.gen

namespace Examples.«system-verilog».comb_ovr.comb_proof

/-- The function the design computes: the highest requesting line among `r[1..3]`, else 0. -/
def prio (r : BitVec 4) : BitVec 2 :=
  if r.getLsbD 3 then 3 else if r.getLsbD 2 then 2 else if r.getLsbD 1 then 1 else 0

/-- The structure theorem of `prio_enc`. -/
theorem prio_struct : ∃ d', prio_enc.sem.lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

/-- **The encoder, proved**: in every settled state of the lowered design whose `r` is `r`, `y` is `prio r`. -/
theorem prio_settles {d' : Design2} (_hl : prio_enc.sem.lowerComb = some d') (_hc : CombDesign d')
    (_ha : Acyclic d') (st : SvState) (_heqs : CombEqs d' st) (_hsh : StateShape d' st) (r : BitVec 4)
    (hr : SvState.lookup st "r" = some (LVec.ofBitVec r)) :
    SvState.lookup st "y" = some (LVec.ofBitVec (prio r)) := by
  sv_equations
  · obtain ⟨⟨vs, hvs, hvsw⟩, -⟩ := known_y_1 0 (by simp)
    have hks : ∀ k, k < 2 → KnownBit st "y" k := fun k hk => (known_y_1 k (by simp; omega)).2
    have hvy := SvState.lookup_eq_ofBitVec_bv hvs (by simpa using hvsw) hks
    rw [hvy] at hvs
    rw [hvs]
    have hb : ∀ j, j < 4 → st.boolAt "r" j = r.getLsbD j := fun j hj => SvState.boolAt_ofBitVec hr hj
    have e : XF.bv 2 (st.boolAt "y") = prio r := by
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [XF.getLsbD_bv hi, eq_y_1 i (by simp; omega)]
      have h3 := hb 3 (by omega)
      have h2 := hb 2 (by omega)
      have h1 := hb 1 (by omega)
      simp only [show Int.toNat 3 = 3 from rfl, show Int.toNat 2 = 2 from rfl, show Int.toNat 1 = 1 from rfl,
        h3, h2, h1]
      unfold prio
      generalize r.getLsbD 3 = b3
      generalize r.getLsbD 2 = b2
      generalize r.getLsbD 1 = b1
      obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
      all_goals cases b3 <;> cases b2 <;> cases b1 <;> decide
    rw [e]
  case inputsKnown => exact inKnown_ofBitVec hr (by omega)

/-- info: 'Examples.«system-verilog».comb_ovr.comb_proof.prio_settles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms prio_settles

end Examples.«system-verilog».comb_ovr.comb_proof
