import Examples.«system-verilog».lp_add.gen
import Examples.«system-verilog».ripple_add.comb_proof
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

/-!
# The ripple-carry adder with LOCALPARAMS, for every `N ≥ 1`, by `sv_structure` + `sv_equations`

`lp_add.sv` is `ripple_add.sv` with its sizes spelled through `localparam integer`s of `N` (see
`gen.lean`): the loop runs to `T = 2 * ((N + 1) / 2) - N % 2` and the carry vector is `[T:0]`. The
theorem is the ripple adder's (`ripple_add/comb_proof.lean`), and so is the whole arithmetic
(`ripple_final` is imported from there): the only new lines are the three places where a
localparam-sized bound meets the plain `N`, each one `omega` (`T = N`, from the definitions of `H` and
`R` as `omega` reads them: floor `/` and `%` by a literal, the truncating forms having been rewritten
under `hN` by the tactic).
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq
open Examples.«system-verilog».lp_add.gen
open Examples.«system-verilog».ripple_add.comb_proof (ripple_final)

namespace Examples.«system-verilog».lp_add.comb_proof

set_option maxHeartbeats 1000000 in
/-- **Ripple-adder correctness with localparams, every `N ≥ 1`.** (The default 200000 heartbeats are
not enough: the tactics' own `simp` and `omega` carry the quotient and remainder of the definitions.) -/
theorem lp_correct (N : Nat) (hN : 1 ≤ N) :
    lp_add.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
        SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
        SvState.lookup st "cout" =
          some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) := by
  have hc : CombDesign (lp_add.sem N) := by
    sv_structure
    all_goals (intros; omega)
  have ha : Acyclic (lp_add.sem N) := by
    sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y ci hA hB hCi
  sv_equations
  · obtain ⟨⟨vs, hvs, hvsw⟩, -⟩ := known_s_g_bit_0 0 (by omega)
    obtain ⟨⟨vc, hvc, hvcw⟩, hkc⟩ := known_cout_plain_1
    exact ripple_final hN hA hB hCi eq_c_plain_0 (fun i hi => eq_c_g_bit_1 i (by omega))
      (fun i hi => eq_s_g_bit_0 i (by omega)) eq_cout_plain_1 hvs
      (by omega) (fun k hk => (known_s_g_bit_0 k (by omega)).2) hvc hvcw hkc
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hCi ?_; omega)

/-- info: 'Examples.«system-verilog».lp_add.comb_proof.lp_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lp_correct

end Examples.«system-verilog».lp_add.comb_proof
