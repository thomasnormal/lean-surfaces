import Examples.«system-verilog».comb_shift.gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombProcTactic
import LeanModels.Sv.CombWordPins

/-!
# Shifts of an operation, for every width, by `sv_structure` + `sv_equations`

The left operand of a shift is context-determined (IEEE 1800-2023 §11.6.1): `instExpr2` lowers it through
`instDivOperand2` at the wider of the context and its own width, every leaf extended there first. `sv_equations` states
the shift over the bit function of the operand at that width (`XF.shlBits` / `XF.shrBits` of `XF.addBits`, of a
bitwise mix, ...); `XF.bv_shlBits_gen` and `XF.bv_shrBits` turn it into `BitVec` shifting.

* `shift_op_correct`: the downstream repro, `y = (a + b) << 2` is `(a + b) <<< 2`;
* `shift_ops_correct`: `c = (a + b) << 1` into `W+1` bits keeps the carry of the sum
  (`(a.setWidth (W+1) + b.setWidth (W+1)) <<< 1`), `x = (a ^ b) >> s`, `m = (a & ~b) << s`;
* `shift_proc_settles`: `y = (a - b) << 1` inside `always_comb`, in every settled state of the lowered design;
* `shift_parts_correct`: shifts whose left operand holds the self-determined sub-operands slang wraps in conversion
  markers: `{a, b} >> s` is `(a ++ b) >>> s`, `{1'b1, a} >> 1` is `(cons true a) >>> 1`, `(c ? a : b) << 1`, `(!a) << 2`,
  `(&a) << s`, `(a == 0) << 1` (computed at `max W 32` bits), `((a > b) + a) << s` into `W+1` bits (the carry kept) and
  `(sa + b) >> 1` of a signed `sa` (its bits, unsigned in the sum);
* `shift_signed_correct`: `(a + b) >>> 1` of signed operands is `BitVec.sshiftRight` of the sum, `a >>> s` into `W+1`
  bits is `sshiftRight` of the sign extension, and `a[W-1:1] >> s` of a signed `a` is the logical shift of
  `extractLsb' 1 (W-1)`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».comb_shift.gen

namespace Examples.«system-verilog».comb_shift.comb_proof

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

/-- A `W`-bit bit function zero-extended at `W` bits reads as itself. -/
theorem bv_zext_self {W : Nat} (f : Nat → Bool) : XF.bv W (fun x => XF.zext W f x) = XF.bv W f :=
  XF.bv_congr_lt (fun k hk => by simp [XF.zext, hk])

/-- The bitwise `^` of two zero-extended `W`-bit operands, read at `W` bits. -/
theorem bv_xor_zext {W : Nat} (f g : Nat → Bool) :
    XF.bv W (fun x => XF.zext W f x ^^ XF.zext W g x) = XF.bv W f ^^^ XF.bv W g := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [XF.getLsbD_bv hi, BitVec.getLsbD_xor, XF.getLsbD_bv hi, XF.getLsbD_bv hi]
  simp [XF.zext, hi]

/-- `a & ~b` of two zero-extended `W`-bit operands, read at `W` bits. -/
theorem bv_and_not_zext {W : Nat} (f g : Nat → Bool) :
    XF.bv W (fun x => XF.zext W f x && !XF.zext W g x) = XF.bv W f &&& ~~~XF.bv W g := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [XF.getLsbD_bv hi, BitVec.getLsbD_and, BitVec.getLsbD_not, XF.getLsbD_bv hi, XF.getLsbD_bv hi]
  simp [XF.zext, hi]

theorem toNat_ofInt32_one : (BitVec.ofInt 32 1).toNat = 1 := by decide

theorem toNat_ofInt32_two : (BitVec.ofInt 32 2).toNat = 2 := by decide

/-- **The downstream repro**: `y = (a + b) << 2` is `(a + b) <<< 2`, for every width `W ≥ 1` in the `int` range. -/
theorem shift_op_correct (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) :
    shift_op.sem W ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (u v : BitVec W), SvState.lookup st "a" = some (LVec.ofBitVec u) →
        SvState.lookup st "b" = some (LVec.ofBitVec v) →
        SvState.lookup st "y" = some (LVec.ofBitVec ((u + v) <<< 2)) := by
  obtain ⟨hc, ha⟩ : CombDesign (shift_op.sem W) ∧ Acyclic (shift_op.sem W) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro u v hA hB
  sv_equations
  · have hWd : (↑W + -1 : Int).natAbs + 1 = W := by omega
    rw [hWd] at eq_y_1 known_y_1
    rw [lookup_bv known_y_1 (by omega), XF.bv_congr_lt eq_y_1, XF.bv_shlBits_gen,
      XF.bv_addBits (fun k _ => rfl), bv_zext_self, bv_zext_self, bv_of_lookup hA, bv_of_lookup hB,
      XF.bv_constBit, toNat_ofInt32_two]
  all_goals first
    | (intros; omega)
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)

/-- **Shifts of an operation into a wider target and by a run-time amount**, for every width `W ≥ 1` in the `int`
range: the sum shifted into `W+1` bits keeps its carry, and `^` / `& ~` shifted by `s` are the `BitVec` shifts. -/
theorem shift_ops_correct (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) :
    shift_ops.sem W ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (u v : BitVec W) (sv : BitVec 3), SvState.lookup st "a" = some (LVec.ofBitVec u) →
        SvState.lookup st "b" = some (LVec.ofBitVec v) →
        SvState.lookup st "s" = some (LVec.ofBitVec sv) →
        SvState.lookup st "c" = some (LVec.ofBitVec ((u.setWidth (W + 1) + v.setWidth (W + 1)) <<< 1)) ∧
        SvState.lookup st "x" = some (LVec.ofBitVec ((u ^^^ v) >>> sv.toNat)) ∧
        SvState.lookup st "m" = some (LVec.ofBitVec ((u &&& ~~~v) <<< sv.toNat)) := by
  obtain ⟨hc, ha⟩ : CombDesign (shift_ops.sem W) ∧ Acyclic (shift_ops.sem W) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro u v sv hA hB hS
  sv_equations
  · have hWd : (↑W + -1 : Int).natAbs + 1 = W := by omega
    have h3 : Int.natAbs 2 + 1 = 3 := rfl
    have hmx : max (W + 1) W = W + 1 := by omega
    rw [hWd] at eq_c_1 eq_x_1 eq_m_1 known_x_1 known_m_1
    rw [hmx] at eq_c_1
    rw [h3] at eq_x_1 eq_m_1
    refine ⟨?_, ?_, ?_⟩
    · rw [lookup_bv known_c_1 (by omega), XF.bv_congr_lt eq_c_1, XF.bv_shlBits_gen,
        XF.bv_addBits (fun k _ => rfl), XF.bv_zext _ (by omega), XF.bv_zext _ (by omega), bv_of_lookup hA,
        bv_of_lookup hB, XF.bv_constBit, toNat_ofInt32_one]
    · rw [lookup_bv known_x_1 (by omega), XF.bv_congr_lt eq_x_1, XF.bv_shrBits, bv_xor_zext, bv_of_lookup hA,
        bv_of_lookup hB, bv_of_lookup hS, BitVec.setWidth_eq]
    · rw [lookup_bv known_m_1 (by omega), XF.bv_congr_lt eq_m_1, XF.bv_shlBits_gen, bv_and_not_zext,
        bv_of_lookup hA, bv_of_lookup hB, bv_of_lookup hS]
  all_goals first
    | (intros; omega)
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hS ?_; omega)

/-- The structure of `shift_proc` (the shift of an operation inside `always_comb`), for every width. -/
theorem shift_proc_struct (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) :
    ∃ d', (shift_proc.sem W).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d' := by
  sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
  all_goals (intros; omega)

/-- **`y = (a - b) << 1` inside `always_comb`**, for every width, in every settled state of the lowered design. -/
theorem shift_proc_settles (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648)
    {d' : Design2} (_hl : (shift_proc.sem W).lowerComb = some d') (_hc : CombDesign d') (_ha : Acyclic d')
    (st : SvState) (_heqs : CombEqs d' st) (_hsh : StateShape d' st) (u v : BitVec W)
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec u)) (hB : SvState.lookup st "b" = some (LVec.ofBitVec v)) :
    SvState.lookup st "y" = some (LVec.ofBitVec ((u - v) <<< 1)) := by
  sv_equations
  · have hWd : (↑W + -1 : Int).natAbs + 1 = W := by omega
    rw [hWd] at eq_y_1 known_y_1
    rw [lookup_bv known_y_1 (by omega), XF.bv_congr_lt eq_y_1, XF.bv_shlBits_gen,
      XF.bv_subBits (fun k _ => rfl), bv_zext_self, bv_zext_self, bv_of_lookup hA, bv_of_lookup hB,
      XF.bv_constBit, toNat_ofInt32_one]
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)

/-- The one-bit literal `1'b1` read as a bit function: `1#1`. -/
theorem bv_lit1 : XF.bv 1 (fun j => ({ bits := #[Logic.l1] } : LVec).boolAt j) = 1#1 := by decide

/-- `{1'b1, a} >> 1` read at `W + 1` bits is the right shift of `BitVec.cons true a`. -/
theorem cons_shr (W : Nat) (u : BitVec W) :
    ((1#1 ++ u) >>> 1).setWidth (W + 1) = (BitVec.cons true u) >>> 1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_append, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_cons]
  by_cases h1 : 1 + i < W
  · rw [if_pos h1, if_neg (show 1 + i ≠ W by omega)]
    simp [hi]
  · rw [if_neg h1]
    by_cases h2 : 1 + i = W
    · rw [if_pos h2, h2, Nat.sub_self]
      simp [hi]
    · rw [if_neg h2, BitVec.getLsbD_of_ge u (1 + i) (by omega)]
      have : (1#1).getLsbD (1 + i - W) = false := BitVec.getLsbD_of_ge _ _ (by omega)
      rw [this]
      simp

/-- `a == 0` at a width `M ≥ W` (both operands zero-extended there) is `a == 0` at `W`. -/
theorem setWidth_beq_zero {W M : Nat} (h : W ≤ M) (u : BitVec W) :
    (u.setWidth M == (BitVec.ofInt 32 0).setWidth M) = (u == 0#W) := by
  have h0 : (BitVec.ofInt 32 0).setWidth M = 0#M := by
    apply BitVec.eq_of_toNat_eq; simp
  rw [h0]
  by_cases hu : u = 0#W
  · subst hu; simp
  · have : u.setWidth M ≠ 0#M := by
      intro h1
      apply hu
      apply BitVec.eq_of_toNat_eq
      have := congrArg BitVec.toNat h1
      rw [BitVec.toNat_setWidth, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le u.isLt (Nat.pow_le_pow_right (by omega) h))]
        at this
      simpa using this
    have e1 : (u.setWidth M == 0#M) = false := by simpa using this
    have e2 : (u == 0#W) = false := by simpa using hu
    rw [e1, e2]

/-- **Shifts whose left operand holds marked self-determined sub-operands** (the concatenation, the condition of `?:`,
`!`, a reduction, a comparison with a constant, a comparison inside a sum, a signed signal inside an unsigned sum), for
every width `W ≥ 1` in the `int` range. -/
theorem shift_parts_correct (W : Nat) (hW : 1 ≤ W) (hR : (W : Int) < 2147483648) :
    shift_parts.sem W ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (u v su : BitVec W) (cv : BitVec 1) (sv : BitVec 3), SvState.lookup st "a" = some (LVec.ofBitVec u) →
        SvState.lookup st "b" = some (LVec.ofBitVec v) →
        SvState.lookup st "c" = some (LVec.ofBitVec cv) →
        SvState.lookup st "s" = some (LVec.ofBitVec sv) →
        SvState.lookup st "sa" = some (LVec.ofBitVec su) →
        SvState.lookup st "y_cat" = some (LVec.ofBitVec ((u ++ v) >>> sv.toNat)) ∧
        SvState.lookup st "y_one" = some (LVec.ofBitVec ((BitVec.cons true u) >>> 1)) ∧
        SvState.lookup st "y_tern" = some (LVec.ofBitVec ((if cv.getLsbD 0 then u else v) <<< 1)) ∧
        SvState.lookup st "y_lnot" = some (LVec.ofBitVec ((BitVec.ofBool (u == 0#W)).setWidth W <<< 2)) ∧
        SvState.lookup st "y_red" =
          some (LVec.ofBitVec ((BitVec.ofBool (u == BitVec.allOnes W)).setWidth W <<< sv.toNat)) ∧
        SvState.lookup st "y_eqz" = some (LVec.ofBitVec ((BitVec.ofBool (u == 0#W)).setWidth W <<< 1)) ∧
        SvState.lookup st "y_cmp" =
          some (LVec.ofBitVec (((BitVec.ofBool (v < u)).setWidth (W + 1) + u.setWidth (W + 1)) <<< sv.toNat)) ∧
        SvState.lookup st "y_sgn" = some (LVec.ofBitVec ((su + v) >>> 1)) := by
  obtain ⟨hc, ha⟩ : CombDesign (shift_parts.sem W) ∧ Acyclic (shift_parts.sem W) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro u v su cv sv hA hB hC hS hSA
  sv_equations
  · have hWd : (↑W + -1 : Int).natAbs + 1 = W := by omega
    have hWW : (↑W + ↑W + -1 : Int).natAbs + 1 = W + W := by omega
    have h3 : Int.natAbs 2 + 1 = 3 := rfl
    have hM : max (W + 1) (max 1 W) = W + 1 := by omega
    simp only [hWd, hWW, h3] at eq_y_cat_1 eq_y_one_1 eq_y_tern_1 eq_y_lnot_1 eq_y_red_1 eq_y_eqz_1 eq_y_cmp_1 eq_y_sgn_1
    simp only [hWd, hWW] at known_y_cat_1 known_y_tern_1 known_y_lnot_1 known_y_red_1 known_y_eqz_1 known_y_sgn_1
    simp only [hM] at eq_y_cmp_1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [lookup_bv known_y_cat_1 (by omega), XF.bv_congr_lt eq_y_cat_1, XF.bv_shrBits, BitVec.setWidth_eq,
        XF.bv_cat2, bv_of_lookup hA, bv_of_lookup hB, bv_of_lookup hS]
    · rw [show ({ bits := #[Logic.l1] } : LVec).width = 1 from rfl] at eq_y_one_1
      rw [lookup_bv known_y_one_1 (by omega), XF.bv_congr_lt eq_y_one_1, XF.bv_shrBits, XF.bv_cat2, bv_lit1,
        bv_of_lookup hA, XF.bv_constBit, toNat_ofInt32_one, cons_shr]
    · have hcb : st.boolAt "c" 0 = cv.getLsbD 0 := by rw [← bv_of_lookup hC, XF.getLsbD_bv (by omega)]
      rw [lookup_bv known_y_tern_1 (by omega), XF.bv_congr_lt eq_y_tern_1, XF.bv_shlBits_gen, hcb,
        XF.bv_constBit, toNat_ofInt32_one]
      by_cases hcv : cv.getLsbD 0 = true
      · simp only [hcv, if_true]
        rw [bv_zext_self, bv_of_lookup hA]
      · simp only [hcv, Bool.false_eq_true, if_false]
        rw [bv_zext_self, bv_of_lookup hB]
    · rw [lookup_bv known_y_lnot_1 (by omega), XF.bv_congr_lt eq_y_lnot_1, XF.bv_shlBits, XF.bv_one,
        XF.any_eq_bv, bv_of_lookup hA, XF.bv_constBit, toNat_ofInt32_two]
      simp only [bne, Bool.not_not]
    · rw [lookup_bv known_y_red_1 (by omega), XF.bv_congr_lt eq_y_red_1, XF.bv_shlBits, XF.bv_one,
        XF.all_eq_bv, bv_of_lookup hA, bv_of_lookup hS]
    · rw [lookup_bv known_y_eqz_1 (by omega), XF.bv_congr_lt eq_y_eqz_1, XF.bv_shlBits, XF.bv_one,
        XF.eqv_eq_bv, XF.bv_zext _ (by omega), XF.bv_zext _ (by omega), XF.bv_constBit, bv_of_lookup hA,
        setWidth_beq_zero (by omega), XF.bv_constBit, toNat_ofInt32_one]
    · rw [lookup_bv known_y_cmp_1 (by omega), XF.bv_congr_lt eq_y_cmp_1, XF.bv_shlBits_gen,
        XF.bv_addBits (fun k _ => rfl), XF.bv_zext _ (by omega), XF.bv_zext _ (by omega), XF.bv_one,
        XF.val_zext _ _ _ (Nat.le_refl _), XF.val_zext _ _ _ (Nat.le_refl _)]
      simp only [gt_iff_lt]
      rw [XF.lt_bv, bv_of_lookup hA, bv_of_lookup hB, bv_of_lookup hS]
    · rw [lookup_bv known_y_sgn_1 (by omega), XF.bv_congr_lt eq_y_sgn_1, XF.bv_shrBits, BitVec.setWidth_eq,
        XF.bv_addBits (fun k _ => rfl), bv_zext_self, bv_zext_self, bv_of_lookup hSA, bv_of_lookup hB,
        XF.bv_constBit, toNat_ofInt32_one]
  all_goals first
    | (intros; omega)
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hC ?_; omega)
    | (refine inKnown_ofBitVec hS ?_; omega)
    | (refine inKnown_ofBitVec hSA ?_; omega)

/-- The bits `[W-1:1]` of a signal, as the bit function shifted down by one: `BitVec.extractLsb'`. -/
theorem bv_sel_hi {W : Nat} (u : BitVec W) (f : Nat → Bool) (hf : XF.bv W f = u) :
    XF.bv (W - 1) (fun x => f (1 + x)) = u.extractLsb' 1 (W - 1) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [XF.getLsbD_bv hi, BitVec.getLsbD_extractLsb', ← hf, XF.getLsbD_bv (show 1 + i < W by omega)]
  simp [hi]

/-- **Signed shifts**, for every width `W ≥ 2` in the `int` range (`a[W-1:1]` needs two bits): the left operand of `>>>`
as an operation, `>>>` into a wider target (sign extension first), and a select of a signed signal shifted right. -/
theorem shift_signed_correct (W : Nat) (hW : 2 ≤ W) (hR : (W : Int) < 2147483648) :
    shift_signed.sem W ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (u v : BitVec W) (sv : BitVec 3), SvState.lookup st "a" = some (LVec.ofBitVec u) →
        SvState.lookup st "b" = some (LVec.ofBitVec v) →
        SvState.lookup st "s" = some (LVec.ofBitVec sv) →
        SvState.lookup st "y_sum" = some (LVec.ofBitVec ((u + v).sshiftRight 1)) ∧
        SvState.lookup st "y_wide" = some (LVec.ofBitVec ((u.signExtend (W + 1)).sshiftRight sv.toNat)) ∧
        SvState.lookup st "y_sel" = some (LVec.ofBitVec ((u.extractLsb' 1 (W - 1)) >>> sv.toNat)) := by
  obtain ⟨hc, ha⟩ : CombDesign (shift_signed.sem W) ∧ Acyclic (shift_signed.sem W) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro u v sv hA hB hS
  sv_equations
  · have hWd : (↑W + -1 : Int).natAbs + 1 = W := by omega
    have hW2 : (↑W + -2 : Int).natAbs + 1 = W - 1 := by omega
    have hWt : (↑W + -1 : Int).toNat = W - 1 := by omega
    have h3 : Int.natAbs 2 + 1 = 3 := rfl
    have h1 : Int.toNat 1 = 1 := rfl
    have hM : max (W + 1) W = W + 1 := by omega
    simp only [hWd, hW2, hWt, h3, h1] at eq_y_sum_1 eq_y_wide_1 eq_y_sel_1 known_y_sum_1 known_y_sel_1
    simp only [hM] at eq_y_wide_1
    refine ⟨?_, ?_, ?_⟩
    · rw [lookup_bv known_y_sum_1 (by omega), XF.bv_congr_lt eq_y_sum_1, XF.bv_ashrBits,
        XF.bv_addBits (fun k _ => rfl), XF.bv_sext_self, XF.bv_sext_self, bv_of_lookup hA, bv_of_lookup hB,
        XF.bv_constBit, toNat_ofInt32_one]
    · rw [lookup_bv known_y_wide_1 (by omega), XF.bv_congr_lt eq_y_wide_1, XF.bv_ashrBits, XF.bv_sext,
        bv_of_lookup hA, bv_of_lookup hS]
    · rw [lookup_bv known_y_sel_1 (by omega), XF.bv_congr_lt eq_y_sel_1, XF.bv_shrBits, BitVec.setWidth_eq,
        bv_sel_hi u _ (bv_of_lookup hA), bv_of_lookup hS]
  all_goals first
    | (intros; omega)
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hS ?_; omega)

end Examples.«system-verilog».comb_shift.comb_proof

/-- info: 'Examples.«system-verilog».comb_shift.comb_proof.shift_op_correct' depends on axioms: [propext,
 Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.«system-verilog».comb_shift.comb_proof.shift_op_correct

/-- info: 'Examples.«system-verilog».comb_shift.comb_proof.shift_ops_correct' depends on axioms: [propext,
 Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.«system-verilog».comb_shift.comb_proof.shift_ops_correct

/-- info: 'Examples.«system-verilog».comb_shift.comb_proof.shift_proc_settles' depends on axioms: [propext,
 Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.«system-verilog».comb_shift.comb_proof.shift_proc_settles

/-- info: 'Examples.«system-verilog».comb_shift.comb_proof.shift_parts_correct' depends on axioms: [propext,
 Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.«system-verilog».comb_shift.comb_proof.shift_parts_correct

/-- info: 'Examples.«system-verilog».comb_shift.comb_proof.shift_signed_correct' depends on axioms: [propext,
 Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Examples.«system-verilog».comb_shift.comb_proof.shift_signed_correct
