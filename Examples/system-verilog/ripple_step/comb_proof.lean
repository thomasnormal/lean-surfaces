import Examples.«system-verilog».ripple_step.gen
import Examples.«system-verilog».ripple_add.comb_proof

/-!
# The ripple-carry adder with an assignment genvar step, for every `N ≥ 1` (WP-L1)

`ripple_step.sv` writes its generate loop as `for (i = 0; i < N; i = i + 1)`. The extractor lowers
that step to the node `i++` has (`gen.lean` pins that the loaded `PDesign` has the generate items of
`ripple_add`), so the proof tactics read it with no change at all: the proof below is
`Examples/system-verilog/ripple_add/comb_proof.lean`'s, with the design constant replaced. The
player's arithmetic `ripple_final` is that file's (it is about the settled state, not the design).
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq
open Examples.«system-verilog».ripple_step.gen
open Examples.«system-verilog».ripple_add.comb_proof (ripple_final)

namespace Examples.«system-verilog».ripple_step.comb_proof

/-- **Ripple-adder correctness with `i = i + 1`, every `N ≥ 1`** (the statement of
`ripple_add`'s `ripple_correct`, about `ripple_step.sem N`). -/
theorem ripple_step_correct (N : Nat) (hN : 1 ≤ N) :
    ripple_step.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
        SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
        SvState.lookup st "cout" =
          some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) := by
  have hc : CombDesign (ripple_step.sem N) := by
    sv_structure
    all_goals (intros; omega)
  have ha : Acyclic (ripple_step.sem N) := by
    sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y ci hA hB hCi
  sv_equations
  · obtain ⟨⟨vs, hvs, hvsw⟩, -⟩ := known_s_g_bit_0 0 (by omega)
    obtain ⟨⟨vc, hvc, hvcw⟩, hkc⟩ := known_cout_plain_1
    exact ripple_final hN hA hB hCi eq_c_plain_0 eq_c_g_bit_1 eq_s_g_bit_0 eq_cout_plain_1 hvs
      (by omega) (fun k hk => (known_s_g_bit_0 k hk).2) hvc hvcw hkc
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hCi ?_; omega)

/-- info: 'Examples.«system-verilog».ripple_step.comb_proof.ripple_step_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ripple_step_correct

end Examples.«system-verilog».ripple_step.comb_proof
