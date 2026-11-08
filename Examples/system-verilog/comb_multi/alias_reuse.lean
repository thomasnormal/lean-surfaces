import Examples.«system-verilog».comb_multi.gen
import LeanModels.Sv.CombProcTactic

/-!
# The aliases of `add_proc_m` are the aliases of `add_proc` (WP-G S1b, gate d)

`sv_equations` names the equations of a design by their TARGET signal and the ordinal of the window among the
windows that write it: `eq_c_2` is the second window that writes `c`, `eq_s_1` the first that writes `s`. The whole
carry/sum cell in ONE body (`add_proc_m.sv`) writes the same windows, in the same order, as the split design
`add_proc.sv` (a carry cell and a sum assign), so it has the SAME aliases with the SAME statements, and a proof
written against the aliases of the one holds for the other unchanged.

This file is the cheap form of that claim, inside the Examples: it states the five equations and the two
knownness facts the reference proof of `tasks/add/reference/add_proc.lean` consumes (`add_final`'s hypotheses,
verbatim) and closes them with the aliases and the closers that reference proof uses. The full check, the reference
proof itself run against `add_proc_m`, is `tasks/add/reference/add_proc_m.lean` (gate d3).
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».comb_multi.gen

namespace Examples.«system-verilog».comb_multi.alias_reuse

/-- **The reference proof's inputs, from `add_proc_m`**: the five equations (`add_final`'s `e0`, `ep`, `estep`,
`esum`, `eout`) and the knownness of `s` and `cout`, from the aliases `eq_c_1`, `eq_p_1`, `eq_c_2`, `eq_s_1`,
`eq_cout_1`, `known_s_1`, `known_cout_1`, with the same closers for the obligations. -/
theorem add_proc_m_aliases (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648) {d' : Design2}
    (_hl : (add_proc_m.sem N).lowerComb = some d') (_hc : CombDesign d') (_ha : Acyclic d')
    (st : SvState) (_heqs : CombEqs d' st) (_hsh : StateShape d' st) (x y : BitVec N) (c0 : Bool)
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hCi : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool c0))) :
    st.boolAt "c" 0 = st.boolAt "cin" 0 ∧
    (∀ i, i < N → st.boolAt "p" i = (st.boolAt "a" i ^^ st.boolAt "b" i)) ∧
    (∀ i, i < N → st.boolAt "c" (i + 1) =
      if st.boolAt "p" i = true then st.boolAt "c" i else st.boolAt "a" i) ∧
    (∀ i, i < N → st.boolAt "s" i = (st.boolAt "p" i ^^ st.boolAt "c" i)) ∧
    st.boolAt "cout" 0 = st.boolAt "c" N ∧
    (∃ vs : LVec, SvState.lookup st "s" = some vs ∧ vs.width = N ∧ ∀ k, k < N → KnownBit st "s" k) ∧
    (∃ vc : LVec, SvState.lookup st "cout" = some vc ∧ vc.width = 1 ∧ KnownBit st "cout" 0) := by
  sv_equations
  · obtain ⟨⟨vs, hvs, hvsw⟩, -⟩ := known_s_1 0 (by omega)
    obtain ⟨⟨vc, hvc, hvcw⟩, hkc⟩ := known_cout_1
    exact ⟨eq_c_1, eq_p_1, eq_c_2, eq_s_1, eq_cout_1, ⟨vs, hvs, by omega, fun k hk => (known_s_1 k hk).2⟩,
      ⟨vc, hvc, hvcw, hkc⟩⟩
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hCi ?_; omega)

/-- info: 'Examples.«system-verilog».comb_multi.alias_reuse.add_proc_m_aliases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms add_proc_m_aliases

end Examples.«system-verilog».comb_multi.alias_reuse
