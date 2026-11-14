import Examples.«system-verilog».gen_deep.gen
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.Comb2

/-!
# `sv_equations` on generate loops nested three deep (`Examples/system-verilog/gen_deep`)

The equations of the three depths are stated with one quantified index per loop: the copies
`t[i][3*j + k] = a[j] ^ b[i]` (`eq_t_g_k_0`, `∀ i j k`), the ANDs `d[i][j]` of two copies (`eq_d_g_col_1`, `∀ i j`) and
the read `y[i] = d[i][0]` (`eq_y_g_row_1`); together `y[i] = a[0] ^ b[i]`. The inputs are known (`hA`, `hB`); the
cover obligation of a read of `t` names its writers' indices (the copies `k = 0` and `k = 2` of the same cell).

Build: `lake build Examples.«system-verilog».gen_deep.eq_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».gen_deep.gen

namespace Examples.«system-verilog».gen_deep.eq_proof

/-- The output of `gen_deep` in a settled state: `y[i] = a[0] ^ b[i]`. -/
theorem gen_deep_y (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648)
    (hc : CombDesign (gen_deep.sem N)) (ha : Acyclic (gen_deep.sem N))
    (st : SvState) (heqs : CombEqs (gen_deep.sem N) st) (hsh : StateShape (gen_deep.sem N) st)
    (x y : BitVec N)
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y)) :
    ∀ i, i < N → st.boolAt "y" i = (st.boolAt "a" 0 ^^ st.boolAt "b" i) := by
  sv_equations
  · intro i hi
    have h0 := eq_t_g_k_0 i hi 0 (by omega) 0 (by omega)
    have h2 := eq_t_g_k_0 i hi 0 (by omega) 2 (by omega)
    have hd := eq_d_g_col_1 i hi 0 (by omega)
    simp at h0 h2 hd
    rw [eq_y_g_row_1 i hi, hd, h0, h2]
    simp
  all_goals first
    | (intros; omega)
    | sv_cover
    | -- a read of two copies in `t` by `d[i][j]`: the copies `k = 0` and `k = 2` of the same `(i, j)` write them
      (intro i hi0 hiN j hj0 hjN
       refine ⟨⟨i.toNat, by omega, j.toNat, by omega, 0, by omega, ?_, ?_⟩,
         ⟨i.toNat, by omega, j.toNat, by omega, 2, by omega, ?_, ?_⟩⟩ <;>
       simp only [rmN, Int.toNat_of_nonneg hi0, Int.toNat_of_nonneg hj0] <;> omega)
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)

/--
info: 'Examples.«system-verilog».gen_deep.eq_proof.gen_deep_y' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_deep_y

end Examples.«system-verilog».gen_deep.eq_proof
