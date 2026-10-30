import Examples.«system-verilog».ripple_add.comb_proof
import Examples.«system-verilog».ripple_add.comb_bundle

/-!
# The stable names of `sv_equations` (WP-P, P2) and the `CombDesign ∧ Acyclic` bundle, end to end

`sv_equations` names the equations after the generate block and the assign's position in it
(`eq_c_g_bit_1`), so an edit that renames a block or adds an assign above renumbers them. It now also
hands over ALIASES named after the TARGET signal and the ordinal (from 1) of the assign among the
assigns that write that signal: `eq_c_1` is the first assign that writes `c` (`c[0] = cin`), `eq_c_2`
the second (the carry cell of the generate loop), `eq_s_1` the sum cell, `eq_cout_1` the carry-out;
`known_<signal>_<k>` likewise. The generated names stay (debug output, old proofs); the aliases are
copies with the same statements.

This file proves the same `ripple_correct` as `comb_proof.lean` (the old names, the two-theorem
structure) with the new API: the bundle `ripple_struct` of `comb_bundle.lean`, then the aliases in the
call of the arithmetic `ripple_final`. Both proofs build: that is the reversibility check.

Build: `lake build Examples.«system-verilog».ripple_add.comb_alias`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq
open Examples.«system-verilog».ripple_add.gen
open Examples.«system-verilog».ripple_add.comb_proof (ripple_final)
open Examples.«system-verilog».ripple_add.comb_bundle (ripple_struct)

namespace Examples.«system-verilog».ripple_add.comb_alias

theorem ripple_correct (N : Nat) (hN : 1 ≤ N) :
    ripple_add.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
        SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
        SvState.lookup st "cout" =
          some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) := by
  obtain ⟨hc, ha⟩ := ripple_struct N hN
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y ci hA hB hCi
  sv_equations
  · -- the aliases are copies of the generated hypotheses (same statements, `rfl`)
    have h1 : eq_c_1 = eq_c_plain_0 := rfl
    have h2 : eq_c_2 = eq_c_g_bit_1 := rfl
    have h3 : eq_s_1 = eq_s_g_bit_0 := rfl
    have h4 : eq_cout_1 = eq_cout_plain_1 := rfl
    obtain ⟨⟨vs, hvs, hvsw⟩, -⟩ := known_s_1 0 (by omega)
    obtain ⟨⟨vc, hvc, hvcw⟩, hkc⟩ := known_cout_1
    exact ripple_final hN hA hB hCi eq_c_1 eq_c_2 eq_s_1 eq_cout_1 hvs
      (by omega) (fun k hk => (known_s_1 k hk).2) hvc hvcw hkc
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hCi ?_; omega)

/-- info: 'Examples.«system-verilog».ripple_add.comb_alias.ripple_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ripple_correct

end Examples.«system-verilog».ripple_add.comb_alias
