import Examples.«system-verilog».gen_tri.gen
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.Comb2

/-!
# `sv_equations` on generate bounds that name an enclosing genvar (`Examples/system-verilog/gen_tri`)

The equation of a cell of the triangular loop `g_lo` is stated for every row `i < N` and every `j < i + 1`
(`eq_t_g_lo_0`), the bound read at the row; the diagonal read `y[i] = t[i][i]` (`g_row`, position 2) then gives
`y[i] = a[i] & b[0]`. The inputs are known (`hA`, `hB`).

Build: `lake build Examples.«system-verilog».gen_tri.eq_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».gen_tri.gen

namespace Examples.«system-verilog».gen_tri.eq_proof

/-- The diagonal of `gen_tri` in a settled state: `y[i] = a[i] & b[0]`. -/
theorem gen_tri_y (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648)
    (hc : CombDesign (gen_tri.sem N)) (ha : Acyclic (gen_tri.sem N))
    (st : SvState) (heqs : CombEqs (gen_tri.sem N) st) (hsh : StateShape (gen_tri.sem N) st)
    (x y : BitVec N)
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y)) :
    ∀ i, i < N → st.boolAt "y" i = (st.boolAt "a" i && st.boolAt "b" 0) := by
  sv_equations
  · intro i hi
    rw [eq_y_g_row_2 i hi, eq_t_g_lo_0 i hi i (by omega)]
    have e : ((i : Int) + -1 * (i : Int) + -0).toNat = 0 := by omega
    rw [e]
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)

/--
info: 'Examples.«system-verilog».gen_tri.eq_proof.gen_tri_y' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_tri_y

end Examples.«system-verilog».gen_tri.eq_proof
