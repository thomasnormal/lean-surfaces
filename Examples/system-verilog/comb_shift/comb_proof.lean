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
* `shift_proc_settles`: `y = (a - b) << 1` inside `always_comb`, in every settled state of the lowered design.
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
