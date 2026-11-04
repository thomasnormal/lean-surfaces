import Examples.«system-verilog».comb_word.gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib
import LeanModels.Sv.CombWordPins

/-!
# `*` and a `$clog2` localparam, for every `N`, by `sv_structure` + `sv_equations`

`mul_word.sv` multiplies two `N`-bit signals into an `N`-bit target and into a `2N`-bit one. `sv_equations` states the
product like a sum (`comb_proof.lean`), in the nested form of the SystemVerilog over the bit functions of the factors:

    eq_p_1 : ∀ k, k < W → st.boolAt "p" k = XF.mulBits W (st.boolAt "a") W (st.boolAt "b") k
    eq_q_1 : ∀ k, k < 2 * N → st.boolAt "q" k = XF.mulBits (2 * N) (XF.zext W (st.boolAt "a")) (2 * N) (XF.zext W (st.boolAt "b")) k

(up to eta; `W` is the width of an `[N-1:0]` signal): the factors are extended to the CONTEXT width first, as for `+`,
and `XF.bv_mulBits` turns such an equation into `BitVec` multiplication (`XF.val_mulBits` gives the value in `Nat`, the
product modulo `2^w`). The `2N`-bit product is the exact one (`mul_full`).

`sq_chain.sv` bounds a generate loop by a `$clog2` localparam, `L = $clog2(N) + 1`, and squares a row per iteration:
`r[i + 1] = r[i] * r[i]`. The localparam is an opaque atom of the obligations (`↑(clog2 N) + 1`), read by `omega` as an
unknown; the one fact about it an obligation needs is the generate-fuel bound `L ≤ 4 N + 60` (`clog2_le`). The closed
form is one induction over the rows (`sq_chain_gen`, the pattern of `row_chain_gen`): `y = x ^ (2 ^ L) mod 2 ^ N`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq
open Examples.«system-verilog».comb_word.gen

namespace Examples.«system-verilog».comb_word.mul_proof

/-- A signal holding the port value `z` has `XF.bv` equal to `z`. -/
theorem bv_of_lookup {N : Nat} {st : SvState} {n : String} {z : BitVec N}
    (h : SvState.lookup st n = some (LVec.ofBitVec z)) : XF.bv N (st.boolAt n) = z := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [XF.getLsbD_bv hi, SvState.boolAt_ofBitVec h hi]

/-- **`mul_word`**: the `N`-bit product wraps (`BitVec` `*`); the `2N`-bit one multiplies the zero-extended factors. -/
theorem mul_word_final {W W2 N : Nat} (hW : W = N) (hW2 : W2 = 2 * N) {st : SvState} {x y : BitVec N}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (ep : ∀ k, k < W → st.boolAt "p" k = XF.mulBits W (st.boolAt "a") W (st.boolAt "b") k)
    (eq : ∀ k, k < W2 → st.boolAt "q" k =
      XF.mulBits W2 (XF.zext W (st.boolAt "a")) W2 (XF.zext W (st.boolAt "b")) k)
    {vp vq : LVec} (hp : SvState.lookup st "p" = some vp) (hpw : vp.width = W)
    (hq : SvState.lookup st "q" = some vq) (hqw : vq.width = W2)
    (hkp : ∀ k, k < W → KnownBit st "p" k) (hkq : ∀ k, k < W2 → KnownBit st "q" k) :
    SvState.lookup st "p" = some (LVec.ofBitVec (x * y)) ∧
      SvState.lookup st "q" = some (LVec.ofBitVec (x.setWidth (2 * N) * y.setWidth (2 * N))) := by
  subst hW hW2
  rw [SvState.lookup_eq_ofBitVec_bv hp hpw hkp] at hp
  rw [SvState.lookup_eq_ofBitVec_bv hq hqw hkq] at hq
  refine ⟨?_, ?_⟩
  · rw [hp, XF.bv_mulBits ep, bv_of_lookup hA, bv_of_lookup hB]
  · rw [hq, XF.bv_mulBits eq, XF.bv_zext _ (by omega), XF.bv_zext _ (by omega), bv_of_lookup hA,
      bv_of_lookup hB]

/-- The `2N`-bit product of two `N`-bit factors is the exact product: it never wraps. -/
theorem mul_full {N : Nat} (x y : BitVec N) :
    (x.setWidth (2 * N) * y.setWidth (2 * N)).toNat = x.toNat * y.toNat := by
  have hx : x.toNat < 2 ^ (2 * N) := Nat.lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by omega) (by omega))
  have hy : y.toNat < 2 ^ (2 * N) := Nat.lt_of_lt_of_le y.isLt (Nat.pow_le_pow_right (by omega) (by omega))
  have hxy : x.toNat * y.toNat < 2 ^ (2 * N) := by
    have := Nat.mul_lt_mul_of_lt_of_le x.isLt (Nat.le_of_lt y.isLt) (Nat.two_pow_pos N)
    rw [show 2 * N = N + N by omega, Nat.pow_add]
    exact this
  rw [BitVec.toNat_mul, BitVec.toNat_setWidth, BitVec.toNat_setWidth, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy,
    Nat.mod_eq_of_lt hxy]

/-- **`p = a * b` and `q = a * b` into `N` and `2N` bits, every `N ≥ 1`.** -/
theorem mul_word_correct (N : Nat) (hN : 1 ≤ N) :
    mul_word.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N), SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "p" = some (LVec.ofBitVec (x * y)) ∧
        SvState.lookup st "q" = some (LVec.ofBitVec (x.setWidth (2 * N) * y.setWidth (2 * N))) := by
  have hc : CombDesign (mul_word.sem N) := by
    sv_structure
    all_goals (intros; omega)
  have ha : Acyclic (mul_word.sem N) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y hA hB
  sv_equations
  · obtain ⟨⟨vp, hvp, hvpw⟩, -⟩ := known_p_1 0 (by omega)
    obtain ⟨⟨vq, hvq, hvqw⟩, -⟩ := known_q_1 0 (by omega)
    exact mul_word_final (by omega) (by omega) hA hB eq_p_1 eq_q_1 hvp hvpw hvq hvqw
      (fun k hk => (known_p_1 k hk).2) (fun k hk => (known_q_1 k hk).2)
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)

/-- info: 'Examples.«system-verilog».comb_word.mul_proof.mul_word_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mul_word_correct

/-- info: 'Examples.«system-verilog».comb_word.mul_proof.mul_full' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mul_full

/-- **A chain of squared rows** (`sq_chain`): row `0` is `x`, row `i + 1` is row `i` squared modulo `2^N`, `y` is row `L`;
so `y = x ^ (2 ^ L) mod 2 ^ N`. One induction over the rows, on the `Nat` values (`XF.val_mulBits`). -/
theorem sq_chain_gen {N L : Nat} {Wi Li : Int} (hW : Wi = (N : Int)) (hL : Li = (L : Int)) {st : SvState}
    {x : BitVec N} (hA : SvState.lookup st "x" = some (LVec.ofBitVec x))
    (e0 : ∀ k, k < N → st.boolAt "r" k = st.boolAt "x" k)
    (es : ∀ i, i < L → ∀ k, k < N →
      st.boolAt "r" (rmN Wi ((i : Int) + 1) 0 + k) =
        XF.mulBits N (fun j => st.boolAt "r" (rmN Wi (i : Int) 0 + j)) N
          (fun j => st.boolAt "r" (rmN Wi (i : Int) 0 + j)) k)
    (ey : ∀ k, k < N → st.boolAt "y" k = st.boolAt "r" (rmN Wi Li 0 + k))
    {vy : LVec} (hy : SvState.lookup st "y" = some vy) (hyw : vy.width = N)
    (hky : ∀ k, k < N → KnownBit st "y" k) :
    SvState.lookup st "y" = some (LVec.ofBitVec (BitVec.ofNat N (x.toNat ^ 2 ^ L))) := by
  subst hW hL
  have hrow : ∀ i, i ≤ L → XF.val (fun j => st.boolAt "r" (rmN (N : Int) (i : Int) 0 + j)) N =
      x.toNat ^ 2 ^ i % 2 ^ N := by
    intro i
    induction i with
    | zero =>
        intro _
        have e : ((0 : Nat) : Int) = 0 := rfl
        simp only [e, rmN_zero_zero_add]
        rw [XF.val_congr_lt e0, ← XF.toNat_bv, bv_of_lookup hA, Nat.pow_zero, Nat.pow_one,
          Nat.mod_eq_of_lt x.isLt]
    | succ j ih =>
        intro hj
        have e : ((j + 1 : Nat) : Int) = (j : Int) + 1 := by omega
        rw [e, XF.val_congr_lt (es j (by omega)), XF.val_mulBits, ih (by omega), ← Nat.mul_mod, Nat.pow_succ,
          Nat.pow_mul, Nat.pow_two]
  have hxy : XF.bv N (st.boolAt "y") = BitVec.ofNat N (x.toNat ^ 2 ^ L) := by
    apply BitVec.eq_of_toNat_eq
    rw [XF.toNat_bv, XF.val_congr_lt ey, hrow L (Nat.le_refl L), BitVec.toNat_ofNat]
  rw [SvState.lookup_eq_ofBitVec_bv hy hyw hky] at hy
  rw [hy, hxy]

/-- **`$clog2(N) + 1` squarings of `x` modulo `2^N`, every `N ≥ 1`**: a generate loop bounded by a `$clog2` localparam. -/
theorem sq_chain_correct (N : Nat) (hN : 1 ≤ N) :
    sq_chain.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x : BitVec N), SvState.lookup st "x" = some (LVec.ofBitVec x) →
        SvState.lookup st "y" = some (LVec.ofBitVec (BitVec.ofNat N (x.toNat ^ 2 ^ (clog2 N + 1)))) := by
  have hL := clog2_le N
  have hc : CombDesign (sq_chain.sem N) := by
    sv_structure
    all_goals (intros; sv_rowmajor; omega)
  have ha : Acyclic (sq_chain.sem N) := by
    sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else clog2 N + 2) (fun _ _ i => i.toNat + 1))
    all_goals (intros; sv_rowmajor; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x hA
  sv_equations
  · obtain ⟨⟨vy, hvy, hvyw⟩, -⟩ := known_y_plain_1 0 (by omega)
    exact sq_chain_gen (by rfl) (by omega) hA (fun k hk => eq_r_plain_0 k hk)
      (fun i hi k hk => eq_r_g_0 i (by omega) k hk) (fun k hk => eq_y_plain_1 k (by omega)) hvy (by omega)
      (fun k hk => (known_y_plain_1 k (by omega)).2)
  case cover_1 =>
    -- `y = r[L]` reads the row the last squaring writes
    intro k hk
    exact Or.inr ⟨clog2 N, by omega, by omega, by omega⟩
  case cover_2 =>
    intro i hi0 hiL k hk
    by_cases h0 : i = 0
    · left; subst h0; omega
    · right
      refine ⟨i.toNat - 1, by omega, ?_⟩
      have e : (((i.toNat - 1 : Nat) : Int) + 1) = i := by omega
      rw [e]
      omega
  all_goals first
    | (intros; omega)
    | (refine inKnown_ofBitVec hA ?_; omega)

/-- info: 'Examples.«system-verilog».comb_word.mul_proof.sq_chain_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sq_chain_correct

end Examples.«system-verilog».comb_word.mul_proof
