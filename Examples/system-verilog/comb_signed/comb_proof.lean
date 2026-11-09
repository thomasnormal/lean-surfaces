import Examples.«system-verilog».comb_signed.gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombWordPins

/-!
# Signed `+`, `-` and a signed copy, for every width, by `sv_structure` + `sv_equations`

`sadd.sv` reads two signed `W`-bit inputs. Every operand is exactly as wide as its target, so the sum and the difference
are the two's-complement ones (`BitVec` `+` and `-` modulo `2^W`), and the copy of a signed input into an unsigned output
is the same bits. The tactics read the design through its unsigned twin (`gen.lean`); `sv_structure` asks the width
obligation of `sv_equations` besides the structural ones (closed here by `omega` like the others), and `sv_equations`
states the equations of the design as written.

* `sadd_correct`: in every settled state, `s = a + b`, `d = a - b`, `x = a ^ ~b`, `y = a`;
* `pass_correct`: `y = x`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».comb_signed.gen

namespace Examples.«system-verilog».comb_signed.comb_proof

/-- A signal holding the port value `z` has `XF.bv` equal to `z`. -/
theorem bv_of_lookup {N : Nat} {st : SvState} {n : String} {z : BitVec N}
    (h : SvState.lookup st n = some (LVec.ofBitVec z)) : XF.bv N (st.boolAt n) = z := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [XF.getLsbD_bv hi, SvState.boolAt_ofBitVec h hi]

/-- A known signal of width `W` holds the bit vector of its Boolean bits. -/
theorem lookup_bv {st : SvState} {n : String} {W : Nat}
    (hk : ∀ k, k < W → (∃ v, SvState.lookup st n = some v ∧ v.width = W) ∧ KnownBit st n k) (hW : 0 < W) :
    SvState.lookup st n = some (LVec.ofBitVec (XF.bv W (st.boolAt n))) := by
  obtain ⟨⟨v, hv, hvw⟩, -⟩ := hk 0 hW
  have := SvState.lookup_eq_ofBitVec_bv hv hvw (fun k hk' => (hk k hk').2)
  rw [hv, this]

/-- **The signed adder, subtractor, mix and copy**, for every width `W ≥ 1` in the `int` range. -/
theorem sadd_correct (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) :
    sadd.sem W ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (u v : BitVec W), SvState.lookup st "a" = some (LVec.ofBitVec u) →
        SvState.lookup st "b" = some (LVec.ofBitVec v) →
        SvState.lookup st "s" = some (LVec.ofBitVec (u + v)) ∧
        SvState.lookup st "d" = some (LVec.ofBitVec (u - v)) ∧
        SvState.lookup st "x" = some (LVec.ofBitVec (u ^^^ ~~~v)) ∧
        SvState.lookup st "y" = some (LVec.ofBitVec u) := by
  obtain ⟨hc, ha⟩ : CombDesign (sadd.sem W) ∧ Acyclic (sadd.sem W) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro u v hA hB
  sv_equations
  · have hWd : (↑W + -1 : Int).natAbs + 1 = W := by omega
    rw [hWd] at eq_s_1 eq_d_1 eq_x_1 eq_y_1 known_s_1 known_d_1 known_x_1 known_y_1
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [lookup_bv known_s_1 (by omega), XF.bv_addBits eq_s_1, bv_of_lookup hA, bv_of_lookup hB]
    · rw [lookup_bv known_d_1 (by omega), XF.bv_subBits eq_d_1, bv_of_lookup hA, bv_of_lookup hB]
    · rw [lookup_bv known_x_1 (by omega)]
      congr 2
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [XF.getLsbD_bv hi, eq_x_1 i hi, SvState.boolAt_ofBitVec hA hi, SvState.boolAt_ofBitVec hB hi]
      simp [hi]
    · rw [lookup_bv known_y_1 (by omega)]
      congr 2
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [XF.getLsbD_bv hi, eq_y_1 i hi, SvState.boolAt_ofBitVec hA hi]
  all_goals first
    | (intros; omega)
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)

/-- **A signed input copied to an unsigned output**: the same bits, for every width. -/
theorem pass_correct (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) :
    pass.sem W ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (u : BitVec W), SvState.lookup st "x" = some (LVec.ofBitVec u) →
        SvState.lookup st "y" = some (LVec.ofBitVec u) := by
  obtain ⟨hc, ha⟩ : CombDesign (pass.sem W) ∧ Acyclic (pass.sem W) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro u hX
  sv_equations
  · have hWd : (↑W + -1 : Int).natAbs + 1 = W := by omega
    rw [hWd] at eq_y_1 known_y_1
    rw [lookup_bv known_y_1 (by omega)]
    congr 2
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [XF.getLsbD_bv hi, eq_y_1 i hi, SvState.boolAt_ofBitVec hX hi]
  all_goals first
    | (intros; omega)
    | (refine inKnown_ofBitVec hX ?_; omega)

/-- info: 'Examples.«system-verilog».comb_signed.comb_proof.sadd_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sadd_correct

/-- info: 'Examples.«system-verilog».comb_signed.comb_proof.pass_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pass_correct

end Examples.«system-verilog».comb_signed.comb_proof
