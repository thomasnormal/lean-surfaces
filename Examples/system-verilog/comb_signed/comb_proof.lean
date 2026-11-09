import Examples.«system-verilog».comb_signed.gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombWordPins

/-!
# Signed `+`, `-`, a signed copy and the signed comparisons, for every width, by `sv_structure` + `sv_equations`

`sadd.sv` reads two signed `W`-bit inputs. Every operand is exactly as wide as its target, so the sum and the difference
are the two's-complement ones (`BitVec` `+` and `-` modulo `2^W`), and the copy of a signed input into an unsigned output
is the same bits. The tactics read the design through its unsigned twin (`gen.lean`); `sv_structure` asks the width
obligation of `sv_equations` besides the structural ones (closed here by `omega` like the others), and `sv_equations`
states the equations of the design as written. A signed comparison of two signed signals of one width is read as written
(the twin keeps it): its equation is `BitVec.slt`/`BitVec.sle` of the two operands' bit vectors, the two's-complement
order `evalPure2` computes through `LVec.toInt?`.

* `sadd_correct`: in every settled state, `s = a + b`, `d = a - b`, `x = a ^ ~b`, `y = a`;
* `pass_correct`: `y = x`;
* `asr_correct`: `y = a >>> s` is `BitVec.sshiftRight` by `s` read as a natural number, `z = a >>> 1`, `l = a << s` is
  `<<<`; `asr_proc_settles`: the same `>>>` inside `always_comb`;
* `ssel_correct`: selects of signed inputs read the bits of the input (`msb` the sign bit, `low` the low `W - 1`
  bits, `x` the `^` of two bits), and `{a[W-1], a[W-1:1]}` is `BitVec.sshiftRight` by one;
* `scmp_correct`: `lt = a <ₛ b`, `le = a ≤ₛ b`, `gt = b <ₛ a`, `ge = b ≤ₛ a` (`BitVec.slt`/`BitVec.sle`: the operands
  ordered as two's-complement integers, IEEE 1800-2023 §11.4.4).
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

/-- A known one-bit signal whose bit is `b` holds `BitVec.ofBool b`. -/
theorem lookup_bool {st : SvState} {n : String} {b : Bool}
    (hk : (∃ v, SvState.lookup st n = some v ∧ v.width = 1) ∧ KnownBit st n 0) (he : st.boolAt n 0 = b) :
    SvState.lookup st n = some (LVec.ofBitVec (BitVec.ofBool b)) := by
  have hk1 : ∀ k, k < 1 → (∃ v, SvState.lookup st n = some v ∧ v.width = 1) ∧ KnownBit st n k := by
    intro k hk'
    obtain rfl : k = 0 := by omega
    exact hk
  rw [lookup_bv hk1 (by omega)]
  congr 2
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain rfl : i = 0 := by omega
  rw [XF.getLsbD_bv hi, he]
  simp

/-- **The four signed comparisons**, for every width `W ≥ 1` in the `int` range: each is one bit, the order of the
operands as two's-complement integers. -/
theorem scmp_correct (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) :
    scmp.sem W ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (u v : BitVec W), SvState.lookup st "a" = some (LVec.ofBitVec u) →
        SvState.lookup st "b" = some (LVec.ofBitVec v) →
        SvState.lookup st "lt" = some (LVec.ofBitVec (BitVec.ofBool (u.slt v))) ∧
        SvState.lookup st "le" = some (LVec.ofBitVec (BitVec.ofBool (u.sle v))) ∧
        SvState.lookup st "gt" = some (LVec.ofBitVec (BitVec.ofBool (v.slt u))) ∧
        SvState.lookup st "ge" = some (LVec.ofBitVec (BitVec.ofBool (v.sle u))) := by
  obtain ⟨hc, ha⟩ : CombDesign (scmp.sem W) ∧ Acyclic (scmp.sem W) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro u v hA hB
  sv_equations
  · have hWd : (↑W + -1 : Int).natAbs + 1 = W := by omega
    rw [hWd] at eq_lt_1 eq_le_1 eq_gt_1 eq_ge_1
    rw [bv_of_lookup hA, bv_of_lookup hB] at eq_lt_1 eq_le_1 eq_gt_1 eq_ge_1
    exact ⟨lookup_bool known_lt_1 eq_lt_1, lookup_bool known_le_1 eq_le_1, lookup_bool known_gt_1 eq_gt_1,
      lookup_bool known_ge_1 eq_ge_1⟩
  all_goals first
    | (intros; omega)
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)

/-- **The arithmetic shift right and the left shift of a signed operand**, for every width `W ≥ 1` in the `int` range:
`>>>` is `BitVec.sshiftRight` by the amount read as a natural number, `<<` is `<<<`. -/
theorem asr_correct (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) :
    asr.sem W ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (u : BitVec W) (sv : BitVec 3), SvState.lookup st "a" = some (LVec.ofBitVec u) →
        SvState.lookup st "s" = some (LVec.ofBitVec sv) →
        SvState.lookup st "y" = some (LVec.ofBitVec (u.sshiftRight sv.toNat)) ∧
        SvState.lookup st "z" = some (LVec.ofBitVec (u.sshiftRight 1)) ∧
        SvState.lookup st "l" = some (LVec.ofBitVec (u <<< sv.toNat)) := by
  obtain ⟨hc, ha⟩ : CombDesign (asr.sem W) ∧ Acyclic (asr.sem W) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro u sv hA hS
  sv_equations
  · have hWd : (↑W + -1 : Int).natAbs + 1 = W := by omega
    have h3 : Int.natAbs 2 + 1 = 3 := rfl
    rw [hWd] at eq_y_1 eq_z_1 eq_l_1 known_y_1 known_z_1 known_l_1
    rw [h3] at eq_y_1 eq_l_1
    refine ⟨?_, ?_, ?_⟩
    · rw [lookup_bv known_y_1 (by omega), XF.bv_congr_lt eq_y_1, XF.bv_ashrBits, XF.bv_sext_self,
        bv_of_lookup hA, bv_of_lookup hS]
    · rw [lookup_bv known_z_1 (by omega), XF.bv_congr_lt eq_z_1, XF.bv_ashrBits, XF.bv_sext_self,
        bv_of_lookup hA, XF.bv_constBit, show (BitVec.ofInt 32 1).toNat = 1 by decide]
    · rw [lookup_bv known_l_1 (by omega), XF.bv_congr_lt eq_l_1, XF.bv_shlBits_s, bv_of_lookup hA,
        bv_of_lookup hS, BitVec.signExtend_eq]
  all_goals first
    | (intros; omega)
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hS ?_; omega)

/-- The structure of `asr_proc` (`>>>` inside `always_comb`), for every width. -/
theorem asr_proc_struct (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) :
    ∃ d', (asr_proc.sem W).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

/-- **`>>>` inside `always_comb`**, for every width, in every settled state of the lowered design. -/
theorem asr_proc_settles (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648)
    {d' : Design2} (_hl : (asr_proc.sem W).lowerComb = some d') (_hc : CombDesign d') (_ha : Acyclic d')
    (st : SvState) (_heqs : CombEqs d' st) (_hsh : StateShape d' st) (u : BitVec W) (sv : BitVec 3)
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec u)) (hS : SvState.lookup st "s" = some (LVec.ofBitVec sv)) :
    SvState.lookup st "y" = some (LVec.ofBitVec (u.sshiftRight sv.toNat)) := by
  sv_equations
  · have hWd : (↑W + -1 : Int).natAbs + 1 = W := by omega
    have h3 : Int.natAbs 2 + 1 = 3 := rfl
    rw [hWd, h3] at eq_y_1
    rw [hWd] at known_y_1
    rw [lookup_bv known_y_1 (by omega), XF.bv_congr_lt eq_y_1, XF.bv_ashrBits, XF.bv_sext_self,
      bv_of_lookup hA, bv_of_lookup hS]
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hS ?_; omega)

/-- **Selects of a signed signal**, for every width `W ≥ 2` in the `int` range: a select is unsigned, so `msb` is the
sign bit, `low` the low `W - 1` bits, `x` the `^` of two bits, and `{a[W-1], a[W-1:1]}` the arithmetic shift right by
one. -/
theorem ssel_correct (W : Nat) (hW : 2 ≤ W) (hR : (W : Int) < 2147483648) :
    ssel.sem W ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (u v : BitVec W), SvState.lookup st "a" = some (LVec.ofBitVec u) →
        SvState.lookup st "b" = some (LVec.ofBitVec v) →
        SvState.lookup st "msb" = some (LVec.ofBitVec (BitVec.ofBool u.msb)) ∧
        SvState.lookup st "low" = some (LVec.ofBitVec (u.setWidth (W - 1))) ∧
        SvState.lookup st "x" = some (LVec.ofBitVec (BitVec.ofBool (u.getLsbD 0 ^^ v.msb))) ∧
        SvState.lookup st "h" = some (LVec.ofBitVec (u.sshiftRight 1)) := by
  obtain ⟨hc, ha⟩ : CombDesign (ssel.sem W) ∧ Acyclic (ssel.sem W) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro u v hA hB
  sv_equations
  · have hWd : (↑W + -1 : Int).natAbs + 1 = W := by omega
    have hWd2 : (↑W + -2 : Int).natAbs + 1 = W - 1 := by omega
    have hw1 : (↑W + -1 : Int).toNat = W - 1 := by omega
    have hA' : ∀ i, i < W → st.boolAt "a" i = u.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hA hi
    have hB' : ∀ i, i < W → st.boolAt "b" i = v.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hB hi
    rw [hw1] at eq_msb_1 eq_x_1 eq_h_1
    rw [hWd2] at eq_low_1 known_low_1
    rw [hWd] at eq_h_1 known_h_1
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact lookup_bool known_msb_1 (by rw [eq_msb_1, hA' _ (by omega), BitVec.msb_eq_getLsbD_last])
    · rw [lookup_bv known_low_1 (by omega)]
      congr 2
      apply BitVec.eq_of_getLsbD_eq
      intro i hi
      rw [XF.getLsbD_bv hi, eq_low_1 i hi, hA' i (by omega), BitVec.getLsbD_setWidth]
      simp [hi]
    · exact lookup_bool known_x_1
        (by rw [eq_x_1, hA' 0 (by omega), hB' _ (by omega), BitVec.msb_eq_getLsbD_last])
    · rw [lookup_bv known_h_1 (by omega)]
      congr 2
      apply BitVec.eq_of_getLsbD_eq
      intro k hk
      rw [XF.getLsbD_bv hk, eq_h_1 k hk, BitVec.getLsbD_sshiftRight, BitVec.msb_eq_getLsbD_last]
      have hk' : ¬ W ≤ k := by omega
      by_cases hk1 : k < W - 1
      · have e1 : Int.toNat 1 + k = 1 + k := rfl
        rw [if_pos hk1, if_pos (by omega : 1 + k < W), e1, hA' _ (by omega)]
        simp [hk']
      · have e2 : W - 1 + (k - (W - 1)) = W - 1 := by omega
        rw [if_neg hk1, if_neg (by omega : ¬ 1 + k < W), e2, hA' _ (by omega)]
        simp [hk']
  all_goals first
    | (intros; omega)
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)

/-- info: 'Examples.«system-verilog».comb_signed.comb_proof.sadd_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sadd_correct

/-- info: 'Examples.«system-verilog».comb_signed.comb_proof.pass_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms pass_correct

/-- info: 'Examples.«system-verilog».comb_signed.comb_proof.scmp_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scmp_correct

/-- info: 'Examples.«system-verilog».comb_signed.comb_proof.asr_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms asr_correct

/-- info: 'Examples.«system-verilog».comb_signed.comb_proof.asr_proc_settles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms asr_proc_settles

/-- info: 'Examples.«system-verilog».comb_signed.comb_proof.ssel_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ssel_correct

end Examples.«system-verilog».comb_signed.comb_proof
