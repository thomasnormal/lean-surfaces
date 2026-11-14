import Examples.«system-verilog».gen_if.gen
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.Comb2

/-!
# `sv_equations` on conditional generate constructs (`Examples/system-verilog/gen_if`)

In a settled state each site's equation holds where its arm is instantiated: `sv_equations` states it under the
arm's guard (`eq_s_g_bit_0 : ∀ i < N, 1 ≤ i → s[i] = a[i] ^^ b[i - 1]`, `eq_s_g_bit_1` under `¬ 1 ≤ i`, the `else if`
arm of `y` under `¬ i = 0` and `¬ i = N - 1`). The read inputs are known (`hA`, `hB`, `hCi`); the cover obligations
of the internal signal `g` are the sites' own (`sv_cover`).

Build: `lake build Examples.«system-verilog».gen_if.eq_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».gen_if.gen

namespace Examples.«system-verilog».gen_if.eq_proof

/-- The low output bits of `gen_if` in a settled state, from the two arms of `g_bit`: `s[0] = a[0] ^ cin` and
`s[i] = a[i] ^ b[i - 1]` above. -/
theorem gen_if_s (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647)
    (hc : CombDesign (gen_if.sem N)) (ha : Acyclic (gen_if.sem N))
    (st : SvState) (heqs : CombEqs (gen_if.sem N) st) (hsh : StateShape (gen_if.sem N) st)
    (x y : BitVec N) (ci : Bool)
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hCi : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci))) :
    st.boolAt "s" 0 = (st.boolAt "a" 0 ^^ st.boolAt "cin" 0) ∧
      ∀ i, i < N → 1 ≤ i → st.boolAt "s" i = (st.boolAt "a" i ^^ st.boolAt "b" (i - 1)) := by
  sv_equations
  · refine ⟨eq_s_g_bit_1 0 (by omega) (by omega), fun i hi h1 => ?_⟩
    rw [eq_s_g_bit_0 i hi (by omega)]
    have e : ((i : Int) + -1).toNat = i - 1 := by omega
    rw [e]
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hCi ?_; omega)

/--
info: 'Examples.«system-verilog».gen_if.eq_proof.gen_if_s' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_if_s

end Examples.«system-verilog».gen_if.eq_proof
