import Examples.«system-verilog».comb_word.gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.Comb2ConcatExample
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib
import LeanModels.Sv.CombWordPins

/-!
# `+`, `-`, comparisons and shifts for every `N ≥ 1`, by `sv_structure` + `sv_equations` (WP-B2)

Four adders and a subtractor written with the word-level operators. The proofs are the shape of
`ripple_add/comb_proof.lean` with ONE different kind of lemma: `sv_equations` states the Boolean value of the
sum in the faithful nested form of the SystemVerilog,

    eq_y_1 : ∀ k, k < W → st.boolAt "y" k = XF.addBits W (st.boolAt "a") W (st.boolAt "b") k
    eq_t_1 : ∀ k, k < N + 1 → st.boolAt "t" k =
               XF.addBits (N + 1) (XF.addBits (N + 1) (XF.zext W (st.boolAt "a")) (N + 1)
                 (XF.zext W (st.boolAt "b"))) (N + 1) (XF.zext 1 (st.boolAt "cin")) k

(`W = (↑N + -1).natAbs + 1` is the width of an `[N-1:0]` signal; `XF.zext n f` is the zero extension that slang's
`Resize` marker computes), and `LeanModels/Sv/CombWord.lean` turns such an equation into `BitVec` arithmetic at a
SYMBOLIC width (`XF.bv_addBits`, `XF.bv_subBits`, `XF.bv_zext`): no carry induction, no case split.

Gate 4a (the last section of the file): whole ROWS of a two-dimensional packed array indexed by a genvar
(`row_chain`, `row_chain_lp`, `row_chain_lit`: a chain `r[i + 1] = ~r[i]`, whose closed form is one induction over the
rows, `row_chain_gen`) and literal-bound or genvar-affine PART SELECTS read and written (`ps_rot`: a rotation by
concatenated part selects, a byte swap by part-select targets, a field; `ps_gen`: `y[4*i+3:4*i] = ~x[4*i+3:4*i]`).
The row-major offset is nonlinear in the stride, so the structure goals close with `sv_rowmajor; omega` as in
`mul_array`, and the two coverage goals of a row chain are closed by naming the writing iteration.

Gate 4b (the last theorem): a GENVAR as the amount of a shift (`shl_gen`: `pp[i] = aw << i`). The amount is a constant
of the instance, the 32-bit literal of its value (`XF.constBit ↑i 32`), and `shl_gen_correct` needs `N ≤ 2^32`: the amount
is read modulo `2^32`.

Gate 4c (the last section): REPLICATION `{N{x}}` of a sized literal or one access that is not a whole signal
(`repl_pad`: zero padding `{ {K{1'b0}}, x }`, the zero extension of `x`; `repl_mask`: the AND mask `a & {N{b[i]}}` of a
partial product). The count is a constant of the instance (a parameter or an affine form over parameters and genvars): its
name is checked in scope by the structural stage, and its non-negativity is a new conjunct of the in-range obligation
that the tactic decides for every example here.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq
open Examples.«system-verilog».comb_word.gen

namespace Examples.«system-verilog».comb_word.comb_proof

/-- A signal holding the port value `z` has `XF.bv` equal to `z`. -/
theorem bv_of_lookup {N : Nat} {st : SvState} {n : String} {z : BitVec N}
    (h : SvState.lookup st n = some (LVec.ofBitVec z)) : XF.bv N (st.boolAt n) = z := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [XF.getLsbD_bv hi, SvState.boolAt_ofBitVec h hi]

/-- **`add_same`**: the equation of `y = a + b` (all three `N` bits wide) is `BitVec` addition. -/
theorem add_same_final {W N : Nat} (hW : W = N) {st : SvState} {x y : BitVec N}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (ey : ∀ k, k < W → st.boolAt "y" k = XF.addBits W (st.boolAt "a") W (st.boolAt "b") k)
    {vy : LVec} (hy : SvState.lookup st "y" = some vy) (hyw : vy.width = W)
    (hky : ∀ k, k < W → KnownBit st "y" k) :
    SvState.lookup st "y" = some (LVec.ofBitVec (x + y)) := by
  subst hW
  rw [SvState.lookup_eq_ofBitVec_bv hy hyw hky] at hy
  rw [hy, XF.bv_addBits ey, bv_of_lookup hA, bv_of_lookup hB]

/-- **`add_wide`**: into an `(N+1)`-bit target, each operand is zero-extended first. -/
theorem add_wide_final {W W' N : Nat} (hW : W = N) (hW' : W' = N + 1) {st : SvState}
    {x y : BitVec N}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (ey : ∀ k, k < W' → st.boolAt "y" k =
      XF.addBits W' (XF.zext W (st.boolAt "a")) W' (XF.zext W (st.boolAt "b")) k)
    {vy : LVec} (hy : SvState.lookup st "y" = some vy) (hyw : vy.width = W')
    (hky : ∀ k, k < W' → KnownBit st "y" k) :
    SvState.lookup st "y" = some (LVec.ofBitVec (x.setWidth (N + 1) + y.setWidth (N + 1))) := by
  subst hW hW'
  rw [SvState.lookup_eq_ofBitVec_bv hy hyw hky] at hy
  rw [hy, XF.bv_addBits ey, XF.bv_zext _ (Nat.le_succ _), XF.bv_zext _ (Nat.le_succ _),
    bv_of_lookup hA, bv_of_lookup hB]

/-- **`sub_wide`**: the same for `-`; the operands are zero-extended, the difference wraps modulo `2^(N+1)`. -/
theorem sub_wide_final {W W' N : Nat} (hW : W = N) (hW' : W' = N + 1) {st : SvState}
    {x y : BitVec N}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (ed : ∀ k, k < W' → st.boolAt "d" k =
      XF.subBits W' (XF.zext W (st.boolAt "a")) W' (XF.zext W (st.boolAt "b")) k)
    {vd : LVec} (hd : SvState.lookup st "d" = some vd) (hdw : vd.width = W')
    (hkd : ∀ k, k < W' → KnownBit st "d" k) :
    SvState.lookup st "d" = some (LVec.ofBitVec (x.setWidth (N + 1) - y.setWidth (N + 1))) := by
  subst hW hW'
  rw [SvState.lookup_eq_ofBitVec_bv hd hdw hkd] at hd
  rw [hd, XF.bv_subBits ed, XF.bv_zext _ (Nat.le_succ _), XF.bv_zext _ (Nat.le_succ _),
    bv_of_lookup hA, bv_of_lookup hB]

/-- **`addp`**: the equation of `if (c) y = a + b; else y = a - b;` (an `if` on the first bit of `c` over the two
word-level leaves) is the choice between the two `BitVec` expressions. -/
theorem addp_final {W W' N : Nat} (hW : W = N) (hW' : W' = N + 1) {st : SvState} {x y : BitVec N}
    {c0 : Bool}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hC : SvState.lookup st "c" = some (LVec.ofBitVec (BitVec.ofBool c0)))
    (ey : ∀ k, k < W' → st.boolAt "y" k =
      if st.boolAt "c" 0 = true then
        XF.addBits W' (XF.zext W (st.boolAt "a")) W' (XF.zext W (st.boolAt "b")) k
      else XF.subBits W' (XF.zext W (st.boolAt "a")) W' (XF.zext W (st.boolAt "b")) k)
    {vy : LVec} (hy : SvState.lookup st "y" = some vy) (hyw : vy.width = W')
    (hky : ∀ k, k < W' → KnownBit st "y" k) :
    SvState.lookup st "y" = some (LVec.ofBitVec
      (if c0 = true then x.setWidth (N + 1) + y.setWidth (N + 1)
        else x.setWidth (N + 1) - y.setWidth (N + 1))) := by
  subst hW hW'
  have hc0 : st.boolAt "c" 0 = c0 := by
    have := SvState.boolAt_ofBitVec hC (i := 0) (by simp)
    simpa using this
  rw [SvState.lookup_eq_ofBitVec_bv hy hyw hky] at hy
  rw [hy]
  congr 2
  cases c0
  · have e : ∀ k, k < W + 1 → st.boolAt "y" k =
        XF.subBits (W + 1) (XF.zext W (st.boolAt "a")) (W + 1) (XF.zext W (st.boolAt "b")) k := by
      intro k hk; rw [ey k hk]; simp [hc0]
    rw [XF.bv_subBits e, XF.bv_zext _ (Nat.le_succ _), XF.bv_zext _ (Nat.le_succ _),
      bv_of_lookup hA, bv_of_lookup hB]
    simp
  · have e : ∀ k, k < W + 1 → st.boolAt "y" k =
        XF.addBits (W + 1) (XF.zext W (st.boolAt "a")) (W + 1) (XF.zext W (st.boolAt "b")) k := by
      intro k hk; rw [ey k hk]; simp [hc0]
    rw [XF.bv_addBits e, XF.bv_zext _ (Nat.le_succ _), XF.bv_zext _ (Nat.le_succ _),
      bv_of_lookup hA, bv_of_lookup hB]
    simp

open Comb2ConcatExample in
/-- **`addw`**: `t = a + b + cin` in an `(N+1)`-bit signal, `s = t[N-1:0]`, `cout = t[N]`. The `(N+1)`-bit sum is
formed ONCE (`bv_addBits` twice, `bv_zext` three times); `cadd_low` and `cadd_carry` (the arithmetic of
`Comb2ConcatExample`, proved for every `N`) read the sum and the carry off it. -/
theorem addw_final {W N : Nat} (hW : W = N) {st : SvState} {x y : BitVec N} {c0 : Bool}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hCi : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool c0)))
    (et : ∀ k, k < N + 1 → st.boolAt "t" k =
      XF.addBits (N + 1)
        (XF.addBits (N + 1) (XF.zext W (st.boolAt "a")) (N + 1) (XF.zext W (st.boolAt "b")))
        (N + 1) (XF.zext 1 (st.boolAt "cin")) k)
    (es : ∀ k, k < W → st.boolAt "s" k = st.boolAt "t" k)
    (eo : st.boolAt "cout" 0 = st.boolAt "t" N)
    {vs : LVec} (hs : SvState.lookup st "s" = some vs) (hsw : vs.width = W)
    (hks : ∀ k, k < W → KnownBit st "s" k)
    {vc : LVec} (hc : SvState.lookup st "cout" = some vc) (hcw : vc.width = 1)
    (hkc : KnownBit st "cout" 0) :
    SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool c0).setWidth N)) ∧
    SvState.lookup st "cout" = some (LVec.ofBitVec
      (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + c0.toNat))) := by
  subst hW
  have hCi1 : XF.bv 1 (st.boolAt "cin") = BitVec.ofBool c0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain rfl : i = 0 := by omega
    rw [XF.getLsbD_bv hi, SvState.boolAt_ofBitVec hCi hi]
  -- (1) the (N+1)-bit sum, once
  have hT : XF.bv (W + 1) (st.boolAt "t") =
      x.setWidth (W + 1) + y.setWidth (W + 1) + (BitVec.ofBool c0).setWidth (W + 1) := by
    rw [XF.bv_addBits et, XF.bv_addBits (fun k _ => rfl), XF.bv_zext _ (Nat.le_succ _),
      XF.bv_zext _ (Nat.le_succ _), XF.bv_zext _ (by omega : 1 ≤ W + 1),
      bv_of_lookup hA, bv_of_lookup hB, hCi1]
  -- (2) `s` and `cout` read the low bits and the top bit of it
  have hsv := SvState.lookup_eq_ofBitVec_bv hs hsw hks
  have hcv := SvState.lookup_eq_ofBitVec_bv hc hcw (fun k hk => by
    obtain rfl : k = 0 := by omega
    exact hkc)
  refine ⟨?_, ?_⟩
  · rw [hsv] at hs
    rw [hs, ← cadd_low, ← hT]
    congr 2
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [XF.getLsbD_bv hi, es i hi, BitVec.getLsbD_extractLsb']
    simp only [Nat.zero_add]
    rw [XF.getLsbD_bv (by omega)]
    simp [hi]
  · rw [hcv] at hc
    rw [hc]
    congr 2
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain rfl : i = 0 := by omega
    rw [XF.getLsbD_bv hi, eo, ← cadd_carry, ← hT, XF.getLsbD_bv (by omega)]
    simp

/-- **`y = a + b`, every `N ≥ 1`.** -/
theorem add_same_correct (N : Nat) (hN : 1 ≤ N) :
    add_same.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N), SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "y" = some (LVec.ofBitVec (x + y)) := by
  have hc : CombDesign (add_same.sem N) := by
    sv_structure
    all_goals (intros; omega)
  have ha : Acyclic (add_same.sem N) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y hA hB
  sv_equations
  · obtain ⟨⟨vy, hvy, hvyw⟩, -⟩ := known_y_1 0 (by omega)
    exact add_same_final (by omega) hA hB eq_y_1 hvy hvyw (fun k hk => (known_y_1 k hk).2)
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)

/-- **`y = a + b` into `N + 1` bits, every `N ≥ 1`.** -/
theorem add_wide_correct (N : Nat) (hN : 1 ≤ N) :
    add_wide.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N), SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "y" =
          some (LVec.ofBitVec (x.setWidth (N + 1) + y.setWidth (N + 1))) := by
  have hc : CombDesign (add_wide.sem N) := by
    sv_structure
    all_goals (intros; omega)
  have ha : Acyclic (add_wide.sem N) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y hA hB
  sv_equations
  · obtain ⟨⟨vy, hvy, hvyw⟩, -⟩ := known_y_1 0 (by omega)
    exact add_wide_final (by omega) (by omega) hA hB eq_y_1 hvy hvyw (fun k hk => (known_y_1 k hk).2)
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)

/-- **`d = a - b` into `N + 1` bits, every `N ≥ 1`.** -/
theorem sub_wide_correct (N : Nat) (hN : 1 ≤ N) :
    sub_wide.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N), SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "d" =
          some (LVec.ofBitVec (x.setWidth (N + 1) - y.setWidth (N + 1))) := by
  have hc : CombDesign (sub_wide.sem N) := by
    sv_structure
    all_goals (intros; omega)
  have ha : Acyclic (sub_wide.sem N) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y hA hB
  sv_equations
  · obtain ⟨⟨vd, hvd, hvdw⟩, -⟩ := known_d_1 0 (by omega)
    exact sub_wide_final (by omega) (by omega) hA hB eq_d_1 hvd hvdw (fun k hk => (known_d_1 k hk).2)
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)

/-- **The adder with a carry-in and a carry-out written with `+`, every `N ≥ 1`** (the statement of
`add_mux_correct`). -/
theorem addw_correct (N : Nat) (hN : 1 ≤ N) :
    addw.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
        SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
        SvState.lookup st "cout" =
          some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) := by
  have hc : CombDesign (addw.sem N) := by
    sv_structure
    all_goals (intros; omega)
  have ha : Acyclic (addw.sem N) := by
    sv_structure (rank := rippleRank (fun p => [0, 1, 1].getD p 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y ci hA hB hCi
  sv_equations
  · obtain ⟨⟨vs, hvs, hvsw⟩, -⟩ := known_s_1 0 (by omega)
    obtain ⟨⟨vc, hvc, hvcw⟩, hkc⟩ := known_cout_1
    exact addw_final (by omega) hA hB hCi eq_t_1 eq_s_1 eq_cout_1 hvs hvsw
      (fun k hk => (known_s_1 k hk).2) hvc hvcw hkc
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hCi ?_; omega)

/-- **`addp`, every `N ≥ 1`, in every settled state of the lowered design** (an `always_comb` whose two leaves are
word-level): `y` is the sum of the zero-extended operands when `c` is set, their difference modulo `2^(N+1)`
otherwise. -/
theorem addp_settles (N : Nat) (hN : 1 ≤ N) {d' : Design2} (_hl : (addp.sem N).lowerComb = some d')
    (_hc : CombDesign d') (_ha : Acyclic d') (st : SvState) (_heqs : CombEqs d' st)
    (_hsh : StateShape d' st) (x y : BitVec N) (c0 : Bool)
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hC : SvState.lookup st "c" = some (LVec.ofBitVec (BitVec.ofBool c0))) :
    SvState.lookup st "y" = some (LVec.ofBitVec
      (if c0 = true then x.setWidth (N + 1) + y.setWidth (N + 1)
        else x.setWidth (N + 1) - y.setWidth (N + 1))) := by
  sv_equations
  · obtain ⟨⟨vy, hvy, hvyw⟩, -⟩ := known_y_1 0 (by omega)
    exact addp_final (by omega) (by omega) hA hB hC eq_y_1 hvy hvyw (fun k hk => (known_y_1 k hk).2)
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hC ?_; omega)

/-- **Comparisons of two `N`-bit operands** (WP-B2 gate 2b): the equation of `lt` is `decide (val a < val b)` over the
`N`-bit window (`W = (↑N + -1).natAbs + 1`), that is `BitVec` `<`; `eq` is `XF.eqv`. -/
theorem cmp_same_final {W N : Nat} (hW : W = N) {st : SvState} {x y : BitVec N}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (el : st.boolAt "lt" 0 = decide (XF.val (fun x => st.boolAt "a" x) W < XF.val (fun x => st.boolAt "b" x) W))
    (ee : st.boolAt "eq" 0 = XF.eqv W (fun x => st.boolAt "a" x) fun x => st.boolAt "b" x) :
    st.boolAt "lt" 0 = decide (x < y) ∧ st.boolAt "eq" 0 = decide (x = y) := by
  subst hW
  constructor
  · rw [el, XF.lt_bv, bv_of_lookup hA, bv_of_lookup hB]
  · rw [ee]
    have h : XF.eqv W (fun x => st.boolAt "a" x) (fun x => st.boolAt "b" x) =
        decide (XF.bv W (st.boolAt "a") = XF.bv W (st.boolAt "b")) := by
      apply Bool.eq_iff_iff.mpr
      simp only [XF.eqv, decide_eq_true_eq]
      constructor
      · intro h
        apply BitVec.eq_of_getLsbD_eq
        intro i hi
        rw [XF.getLsbD_bv hi, XF.getLsbD_bv hi, h i hi]
      · intro h k hk
        have := congrArg (fun v => v.getLsbD k) h
        simpa [XF.getLsbD_bv hk] using this
    rw [h, bv_of_lookup hA, bv_of_lookup hB]

/-- The sum with the constant `1`, formed at a width `M ≥ N` and truncated back to `N` bits, is `x + 1`. -/
theorem setWidth_add_const {N M : Nat} (h : N ≤ M) (x : BitVec N) :
    ((x.setWidth M + BitVec.ofInt M 1).setWidth N) = x + 1 := by
  have e : BitVec.ofInt M 1 = (1 : BitVec M) := by simp
  rw [e, BitVec.setWidth_add _ _ h, BitVec.setWidth_setWidth_of_le _ h, BitVec.setWidth_eq]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]
  exact Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)

/-- **`y1 = a + 1` into `N` bits, `t = a + b` into `N - 1` bits** (WP-B2 gate 2b): the unsized constant makes the sum
32 bits wide (`max N 32`) and slang truncates it; the equation reads the sum at that width and the glue lemmas
`XF.bv_zext_trunc`, `XF.bv_constBit` turn it into `BitVec` arithmetic. -/
theorem trunc_inc_y1_final {W N : Nat} (hW : W = N) {st : SvState} {x : BitVec N}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (ey : ∀ k, k < W → st.boolAt "y1" k =
      if max W 32 < W then
        XF.addBits W (XF.zext W (fun x => st.boolAt "a" x)) W (fun x => XF.constBit 1 W x) k
      else
        XF.zext (max W 32)
          (fun x => XF.addBits (max W 32) (XF.zext W (fun x => st.boolAt "a" x)) (max W 32)
            (fun x => XF.constBit 1 (max W 32) x) x) k)
    {vy : LVec} (hy : SvState.lookup st "y1" = some vy) (hyw : vy.width = W)
    (hky : ∀ k, k < W → KnownBit st "y1" k) :
    SvState.lookup st "y1" = some (LVec.ofBitVec (x + 1)) := by
  subst hW
  have hlt : ¬ max W 32 < W := by omega
  have ey' : ∀ k, k < W → st.boolAt "y1" k =
      XF.zext (max W 32) (fun x => XF.addBits (max W 32) (XF.zext W (fun x => st.boolAt "a" x)) (max W 32)
        (fun x => XF.constBit 1 (max W 32) x) x) k := fun k hk => by rw [ey k hk, if_neg hlt]
  rw [SvState.lookup_eq_ofBitVec_bv hy hyw hky] at hy
  rw [hy]
  congr 1
  have h1 := XF.bv_congr_lt ey'
  rw [h1, XF.bv_zext_trunc (n := max W 32) (m := W) _ (by omega), XF.bv_addBits (fun k _ => rfl),
    XF.bv_zext (n := W) (m := max W 32) _ (by omega), bv_of_lookup hA, XF.bv_constBit]
  exact congrArg LVec.ofBitVec (setWidth_add_const (M := max W 32) (by omega) x)

/-- A one-bit signal whose bit is `b` holds `ofBool b`. -/
theorem bit1_of_lookup {st : SvState} {n : String} {v : LVec} {b : Bool}
    (h : SvState.lookup st n = some v) (hw : v.width = 1) (hk : KnownBit st n 0)
    (hb : st.boolAt n 0 = b) : SvState.lookup st n = some (LVec.ofBitVec (BitVec.ofBool b)) := by
  have hv := SvState.lookup_eq_ofBitVec_bv h hw (fun k hk' => by
    obtain rfl : k = 0 := by omega
    exact hk)
  rw [hv] at h
  rw [h]
  congr 2
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  obtain rfl : i = 0 := by omega
  rw [XF.getLsbD_bv hi, hb]
  simp

/-- **The comparison `<` and `==` of two `N`-bit operands, every `N ≥ 1`.** -/
theorem cmp_same_correct (N : Nat) (hN : 1 ≤ N) :
    cmp_same.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N), SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "lt" = some (LVec.ofBitVec (BitVec.ofBool (decide (x < y)))) ∧
        SvState.lookup st "eq" = some (LVec.ofBitVec (BitVec.ofBool (decide (x = y)))) := by
  have hc : CombDesign (cmp_same.sem N) := by
    sv_structure
    all_goals (intros; omega)
  have ha : Acyclic (cmp_same.sem N) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y hA hB
  sv_equations
  · obtain ⟨⟨vl, hvl, hvlw⟩, hkl⟩ := known_lt_1
    obtain ⟨⟨ve, hve, hvew⟩, hke⟩ := known_eq_1
    have hW : ((N : Int) + -1).natAbs + 1 = N := by omega
    have h := cmp_same_final hW hA hB eq_lt_1 eq_eq_1
    exact ⟨bit1_of_lookup hvl hvlw hkl h.1, bit1_of_lookup hve hvew hke h.2⟩
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)

/-! ### Run-time shifts (WP-B2 gate 3)

`y = a << s` and `y = a >> s` with a RUN-TIME amount: the equation is `XF.shlBits` / `XF.shrBits` over the bit functions of
the operand and of the amount, and `XF.bv_shlBits` / `XF.bv_shrBits` (`LeanModels/Sv/CombWord.lean`, plain Lean, no
induction) turn it into `BitVec` shifting with the amount read as a natural number: an amount of `N` or more gives `0`, as
in the LRM. The left operand is context-determined, so a shift into a wider target extends it BEFORE shifting
(`XF.zext W …`); `1 << s` is a signed shift (`XF.sext 32 …`, `XF.bv_shlBits_s`). -/

/-- The unsized constant `1` as a 32-bit natural number. -/
theorem toNat_ofInt32_one : (BitVec.ofInt 32 1).toNat = 1 := by decide

/-- … and `2`. -/
theorem toNat_ofInt32_two : (BitVec.ofInt 32 2).toNat = 2 := by decide

/-- The signed constant `1` extended from 32 bits to `N ≥ 1` bits is `1`. -/
theorem signExtend_one {N : Nat} (hN : 1 ≤ N) : (BitVec.ofInt 32 1).signExtend N = 1#N := by
  have h1 : BitVec.ofInt 32 1 = 1#32 := by decide
  rw [h1]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_signExtend]
  by_cases h : i < 32
  · simp [h, hi]
  · have hm : (1#32).msb = false := by decide
    simp [h, hi, hm]
    omega

/-- Truncating a shifted `1` (`1#M <<< k`, `N ≤ M`) to `N ≥ 1` bits is shifting the `N`-bit `1`. -/
theorem one_shl_setWidth {M N : Nat} (hN : 1 ≤ N) (hNM : N ≤ M) (k : Nat) :
    ((1#M) <<< k).setWidth N = (1#N) <<< k := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft]
  by_cases h1 : i < k
  · simp [h1, hi]
  · by_cases h2 : i - k = 0
    · simp [h1, hi, h2, show i < M by omega, show 0 < N by omega, show 0 < M by omega]
    · simp [h1, hi, h2, BitVec.getLsbD_one]

/-- **`shl_n`**: the equation of `y = a << s` (`N`-bit operand and target, a 3-bit amount) is `BitVec` `<<<`. -/
theorem shl_n_final {W N S : Nat} (hW : W = N) (hS : S = 3) {st : SvState} {x : BitVec N} {sv : BitVec 3}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hSv : SvState.lookup st "s" = some (LVec.ofBitVec sv))
    (ey : ∀ k, k < W → st.boolAt "y" k =
      XF.shlBits (XF.zext W fun x => st.boolAt "a" x) S (fun x => st.boolAt "s" x) k)
    {vy : LVec} (hy : SvState.lookup st "y" = some vy) (hyw : vy.width = W)
    (hky : ∀ k, k < W → KnownBit st "y" k) :
    SvState.lookup st "y" = some (LVec.ofBitVec (x <<< sv.toNat)) := by
  subst hW hS
  rw [SvState.lookup_eq_ofBitVec_bv hy hyw hky] at hy
  rw [hy, XF.bv_congr_lt ey, XF.bv_shlBits, bv_of_lookup hA, bv_of_lookup hSv, BitVec.setWidth_eq]

/-- **`shr_n`**: `y = a >> s` is `BitVec` `>>>` (a logical shift: zeros come in at the top). -/
theorem shr_n_final {W N S : Nat} (hW : W = N) (hS : S = 3) {st : SvState} {x : BitVec N} {sv : BitVec 3}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hSv : SvState.lookup st "s" = some (LVec.ofBitVec sv))
    (ey : ∀ k, k < W → st.boolAt "y" k =
      XF.shrBits W (fun x => st.boolAt "a" x) S (fun x => st.boolAt "s" x) k)
    {vy : LVec} (hy : SvState.lookup st "y" = some vy) (hyw : vy.width = W)
    (hky : ∀ k, k < W → KnownBit st "y" k) :
    SvState.lookup st "y" = some (LVec.ofBitVec (x >>> sv.toNat)) := by
  subst hW hS
  rw [SvState.lookup_eq_ofBitVec_bv hy hyw hky] at hy
  rw [hy, XF.bv_congr_lt ey, XF.bv_shrBits, bv_of_lookup hA, bv_of_lookup hSv, BitVec.setWidth_eq]

/-- **`shl_wide`**: into an `(N+1)`-bit target the operand is zero-extended BEFORE the shift, so the bit shifted out of the
`N`-bit operand survives. -/
theorem shl_wide_final {W N S : Nat} (hW : W = N) (hS : S = 3) {st : SvState} {x : BitVec N} {sv : BitVec 3}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hSv : SvState.lookup st "s" = some (LVec.ofBitVec sv))
    (ey : ∀ k, k < N + 1 → st.boolAt "y" k =
      XF.shlBits (XF.zext W fun x => st.boolAt "a" x) S (fun x => st.boolAt "s" x) k)
    {vy : LVec} (hy : SvState.lookup st "y" = some vy) (hyw : vy.width = N + 1)
    (hky : ∀ k, k < N + 1 → KnownBit st "y" k) :
    SvState.lookup st "y" = some (LVec.ofBitVec ((x.setWidth (N + 1)) <<< sv.toNat)) := by
  subst hW hS
  rw [SvState.lookup_eq_ofBitVec_bv hy hyw hky] at hy
  rw [hy, XF.bv_congr_lt ey, XF.bv_shlBits, bv_of_lookup hA, bv_of_lookup hSv]

/-- **`onehot`**: `y = 1 << s`. The unsized constant is a SIGNED 32-bit integer, so the shift is computed at `max N 32`
bits with the constant sign-extended (`XF.bv_shlBits_s`), and truncated into the `N`-bit target: for `N > 32` the shift
runs at `N` bits, for `N ≤ 32` at 32 bits and the low `N` are kept (the single `if` of the printed equation). -/
theorem onehot_final {W N S : Nat} (hW : W = N) (hS : S = 3) (hN : 1 ≤ N) {st : SvState} {sv : BitVec 3}
    (hSv : SvState.lookup st "s" = some (LVec.ofBitVec sv))
    (ey : ∀ k, k < W → st.boolAt "y" k =
      if 32 < W then
        XF.shlBits (XF.sext 32 fun x => XF.constBit 1 32 x) S (fun x => st.boolAt "s" x) k
      else
        XF.zext 32
          (fun x => XF.shlBits (XF.sext 32 fun x => XF.constBit 1 32 x) S (fun x => st.boolAt "s" x) x) k)
    {vy : LVec} (hy : SvState.lookup st "y" = some vy) (hyw : vy.width = W)
    (hky : ∀ k, k < W → KnownBit st "y" k) :
    SvState.lookup st "y" = some (LVec.ofBitVec ((1#N) <<< sv.toNat)) := by
  subst hW hS
  rw [SvState.lookup_eq_ofBitVec_bv hy hyw hky] at hy
  by_cases h32 : 32 < W
  · have ey' : ∀ k, k < W → st.boolAt "y" k =
        XF.shlBits (XF.sext 32 fun x => XF.constBit 1 32 x) 3 (fun x => st.boolAt "s" x) k :=
      fun k hk => by rw [ey k hk, if_pos h32]
    rw [hy, XF.bv_congr_lt ey', XF.bv_shlBits_s, XF.bv_constBit, bv_of_lookup hSv, signExtend_one hN]
  · have ey' : ∀ k, k < W → st.boolAt "y" k =
        XF.zext 32 (fun x => XF.shlBits (XF.sext 32 fun x => XF.constBit 1 32 x) 3 (fun x => st.boolAt "s" x) x) k :=
      fun k hk => by rw [ey k hk, if_neg h32]
    have h1 : (BitVec.ofInt 32 1).signExtend 32 = 1#32 := by decide
    rw [hy, XF.bv_congr_lt ey', XF.bv_zext_trunc (n := 32) (m := W) _ (by omega), XF.bv_shlBits_s,
      XF.bv_constBit, bv_of_lookup hSv, h1]
    rw [one_shl_setWidth (M := 32) (N := W) hN (by omega)]

/-- **`shl_const`**: `y = a << 1` and `z = a >> 2`, an unsized constant amount (32 bits wide, it never widens the result). -/
theorem shl_const_final {W N : Nat} (hW : W = N) {st : SvState} {x : BitVec N}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (ey : ∀ k, k < W → st.boolAt "y" k =
      XF.shlBits (XF.zext W fun x => st.boolAt "a" x) 32 (fun x => XF.constBit 1 32 x) k)
    (ez : ∀ k, k < W → st.boolAt "z" k =
      XF.shrBits W (fun x => st.boolAt "a" x) 32 (fun x => XF.constBit 2 32 x) k)
    {vy : LVec} (hy : SvState.lookup st "y" = some vy) (hyw : vy.width = W)
    (hky : ∀ k, k < W → KnownBit st "y" k)
    {vz : LVec} (hz : SvState.lookup st "z" = some vz) (hzw : vz.width = W)
    (hkz : ∀ k, k < W → KnownBit st "z" k) :
    SvState.lookup st "y" = some (LVec.ofBitVec (x <<< 1)) ∧
    SvState.lookup st "z" = some (LVec.ofBitVec (x >>> 2)) := by
  subst hW
  rw [SvState.lookup_eq_ofBitVec_bv hy hyw hky] at hy
  rw [SvState.lookup_eq_ofBitVec_bv hz hzw hkz] at hz
  refine ⟨?_, ?_⟩
  · rw [hy, XF.bv_congr_lt ey, XF.bv_shlBits, bv_of_lookup hA, XF.bv_constBit, toNat_ofInt32_one,
      BitVec.setWidth_eq]
  · rw [hz, XF.bv_congr_lt ez, XF.bv_shrBits, bv_of_lookup hA, XF.bv_constBit, toNat_ofInt32_two,
      BitVec.setWidth_eq]

/-- **`y = a << s`, every `N ≥ 1`** (a barrel shifter with a 3-bit amount). -/
theorem shl_n_correct (N : Nat) (hN : 1 ≤ N) :
    shl_n.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x : BitVec N) (sv : BitVec 3), SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "s" = some (LVec.ofBitVec sv) →
        SvState.lookup st "y" = some (LVec.ofBitVec (x <<< sv.toNat)) := by
  have hc : CombDesign (shl_n.sem N) := by
    sv_structure
    all_goals (intros; omega)
  have ha : Acyclic (shl_n.sem N) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x sv hA hSv
  sv_equations
  · obtain ⟨⟨vy, hvy, hvyw⟩, -⟩ := known_y_1 0 (by omega)
    exact shl_n_final (by omega) (by omega) hA hSv eq_y_1 hvy hvyw (fun k hk => (known_y_1 k hk).2)
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hSv ?_; omega)

/-- **`y = a >> s`, every `N ≥ 1`.** -/
theorem shr_n_correct (N : Nat) (hN : 1 ≤ N) :
    shr_n.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x : BitVec N) (sv : BitVec 3), SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "s" = some (LVec.ofBitVec sv) →
        SvState.lookup st "y" = some (LVec.ofBitVec (x >>> sv.toNat)) := by
  have hc : CombDesign (shr_n.sem N) := by
    sv_structure
    all_goals (intros; omega)
  have ha : Acyclic (shr_n.sem N) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x sv hA hSv
  sv_equations
  · obtain ⟨⟨vy, hvy, hvyw⟩, -⟩ := known_y_1 0 (by omega)
    exact shr_n_final (by omega) (by omega) hA hSv eq_y_1 hvy hvyw (fun k hk => (known_y_1 k hk).2)
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hSv ?_; omega)

/-- **`y = a << s` into `N + 1` bits, every `N ≥ 1`.** -/
theorem shl_wide_correct (N : Nat) (hN : 1 ≤ N) :
    shl_wide.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x : BitVec N) (sv : BitVec 3), SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "s" = some (LVec.ofBitVec sv) →
        SvState.lookup st "y" = some (LVec.ofBitVec ((x.setWidth (N + 1)) <<< sv.toNat)) := by
  have hc : CombDesign (shl_wide.sem N) := by
    sv_structure
    all_goals (intros; omega)
  have ha : Acyclic (shl_wide.sem N) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x sv hA hSv
  sv_equations
  · obtain ⟨⟨vy, hvy, hvyw⟩, -⟩ := known_y_1 0 (by omega)
    exact shl_wide_final (by omega) (by omega) hA hSv eq_y_1 hvy hvyw (fun k hk => (known_y_1 k hk).2)
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hSv ?_; omega)

/-- **The one-hot decoder `y = 1 << s`, every `N ≥ 1`** (`1#N <<< s`: bit `s` is set, and nothing at all when `s ≥ N`). -/
theorem onehot_correct (N : Nat) (hN : 1 ≤ N) :
    onehot.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (sv : BitVec 3), SvState.lookup st "s" = some (LVec.ofBitVec sv) →
        SvState.lookup st "y" = some (LVec.ofBitVec ((1#N) <<< sv.toNat)) := by
  have hc : CombDesign (onehot.sem N) := by
    sv_structure
    all_goals (intros; omega)
  have ha : Acyclic (onehot.sem N) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro sv hSv
  sv_equations
  · obtain ⟨⟨vy, hvy, hvyw⟩, -⟩ := known_y_1 0 (by omega)
    exact onehot_final (by omega) (by omega) hN hSv eq_y_1 hvy hvyw (fun k hk => (known_y_1 k hk).2)
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hSv ?_; omega)

/-- **`y = a << 1`, `z = a >> 2`, every `N ≥ 1`** (shifts by an unsized constant amount). -/
theorem shl_const_correct (N : Nat) (hN : 1 ≤ N) :
    shl_const.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x : BitVec N), SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "y" = some (LVec.ofBitVec (x <<< 1)) ∧
        SvState.lookup st "z" = some (LVec.ofBitVec (x >>> 2)) := by
  have hc : CombDesign (shl_const.sem N) := by
    sv_structure
    all_goals (intros; omega)
  have ha : Acyclic (shl_const.sem N) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x hA
  sv_equations
  · obtain ⟨⟨vy, hvy, hvyw⟩, -⟩ := known_y_1 0 (by omega)
    obtain ⟨⟨vz, hvz, hvzw⟩, -⟩ := known_z_1 0 (by omega)
    exact shl_const_final (by omega) hA eq_y_1 eq_z_1 hvy hvyw (fun k hk => (known_y_1 k hk).2)
      hvz hvzw (fun k hk => (known_z_1 k hk).2)
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)

/-! ### Concatenations as operands (WP-B2 gate 3b)

`{1'b0, a}`, `{b, 1'b0}`, `{a, b}` inside `+`, `?:` and `==`: the equation reads a concatenation as the bit function
`if j < w2 then lo j else hi (j - w2)` (a literal part prints as `false` / `true` or as `LVec.boolAt` of the literal),
and `LeanModels/Sv/CombWord.lean` turns it into `BitVec` operations: `XF.bv_pad` (a zero pad above is `setWidth`) and
`XF.bv_cat2` (`++`); the single-bit literal pads below / above are `BitVec.concat` / `BitVec.cons`. -/

/-- A two-bit zero literal reads as `0` at every index. -/
theorem boolAt_zero2 (j : Nat) : (LVec.mk #[Logic.l0, Logic.l0]).boolAt j = false := by
  rcases j with _ | _ | j <;> simp [LVec.boolAt]

/-- … and the one-bit `1'b1` literal at index `0` reads as `1`. -/
theorem boolAt_one1 {j : Nat} (hj : j = 0) : (LVec.mk #[Logic.l1]).boolAt j = true := by
  subst hj; simp [LVec.boolAt]

/-- `{b, 1'b0}`: the bit function of a zero below `W` bits is `BitVec.concat`. -/
theorem bv_concat_false {W : Nat} (b : Nat → Bool) :
    XF.bv (W + 1) (fun x => if x = 0 then false else b (x - 1)) = (XF.bv W b).concat false := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [XF.getLsbD_bv hk, BitVec.getLsbD_concat]
  by_cases h : k = 0
  · rw [if_pos h, if_pos h]
  · rw [if_neg h, if_neg h, XF.getLsbD_bv (show k - 1 < W by omega)]

/-- `{1'b1, a}`: the bit function of a one above `W` bits is `BitVec.cons`. -/
theorem bv_cons_true {W : Nat} (a : Nat → Bool) :
    XF.bv (W + 1) (fun k => if k < W then a k else true) = BitVec.cons true (XF.bv W a) := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [XF.getLsbD_bv hk, BitVec.getLsbD_cons]
  by_cases h : k < W
  · rw [if_pos h, if_neg (by omega), XF.getLsbD_bv h]
  · rw [if_neg h, if_pos (by omega)]

/-- **`cat_add`, the sum `s = {1'b0, a} + {1'b0, b} + cin`**: two bare concatenations (zero pads, `XF.bv_pad`) and the
zero-extended carry. -/
theorem cat_add_s_final {W N : Nat} (hW : W = N) {st : SvState} {x y : BitVec N} {c0 : Bool}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hCi : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool c0)))
    (es : ∀ k, k < N + 1 → st.boolAt "s" k =
      XF.addBits (N + 1)
        (fun x => XF.addBits (N + 1) (fun x => if x < W then st.boolAt "a" x else false) (N + 1)
          (fun x => if x < W then st.boolAt "b" x else false) x)
        (N + 1) (fun x => XF.zext 1 (fun k => st.boolAt "cin" k) x) k)
    {vs : LVec} (hs : SvState.lookup st "s" = some vs) (hsw : vs.width = N + 1)
    (hks : ∀ k, k < N + 1 → KnownBit st "s" k) :
    SvState.lookup st "s" = some (LVec.ofBitVec
      (x.setWidth (N + 1) + y.setWidth (N + 1) + (BitVec.ofBool c0).setWidth (N + 1))) := by
  subst hW
  have hCi1 : XF.bv 1 (st.boolAt "cin") = BitVec.ofBool c0 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain rfl : i = 0 := by omega
    rw [XF.getLsbD_bv hi, SvState.boolAt_ofBitVec hCi hi]
  rw [SvState.lookup_eq_ofBitVec_bv hs hsw hks] at hs
  rw [hs, XF.bv_addBits es, XF.bv_addBits (fun k _ => rfl), XF.bv_pad (Nat.le_succ _), XF.bv_pad (Nat.le_succ _),
    XF.bv_zext _ (by omega : 1 ≤ W + 1), bv_of_lookup hA, bv_of_lookup hB, hCi1]

/-- **`t = {2'b0, a} + {b, 1'b0}`**: a bare concatenation and one under a `Resize` marker (the `XF.zext (N + 1)` of a
`BitVec.concat`). -/
theorem cat_add_t_final {W W' N : Nat} (hW : W = N) (hW' : W' = N + 2) {st : SvState} {x y : BitVec N}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (et : ∀ k, k < W' → st.boolAt "t" k =
      XF.addBits W'
        (fun x => if x < W then st.boolAt "a" x else (LVec.mk #[Logic.l0, Logic.l0]).boolAt (x - W)) W'
        (fun x => XF.zext (W + 1) (fun x => if x = 0 then false else st.boolAt "b" (x - 1)) x) k)
    {vt : LVec} (ht : SvState.lookup st "t" = some vt) (htw : vt.width = W')
    (hkt : ∀ k, k < W' → KnownBit st "t" k) :
    SvState.lookup st "t" = some (LVec.ofBitVec (x.setWidth (N + 2) + (y.concat false).setWidth (N + 2))) := by
  subst hW hW'
  rw [SvState.lookup_eq_ofBitVec_bv ht htw hkt] at ht
  simp only [boolAt_zero2] at et
  rw [ht, XF.bv_addBits et, XF.bv_pad (Nat.le_add_right _ 2), XF.bv_zext _ (by omega : W + 1 ≤ W + 2),
    bv_concat_false, bv_of_lookup hA, bv_of_lookup hB]

/-- **`w = cin ? {a, 1'b0} : {1'b1, a}`**: the arms of a `?:` are concatenations. -/
theorem cat_add_w_final {W N : Nat} (hW : W = N) {st : SvState} {x : BitVec N} {c0 : Bool}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hCi : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool c0)))
    (ew : ∀ k, k < N + 1 → st.boolAt "w" k =
      if st.boolAt "cin" 0 = true then (if k = 0 then false else st.boolAt "a" (k - 1))
      else if k < W then st.boolAt "a" k else (LVec.mk #[Logic.l1]).boolAt (k - W))
    {vw : LVec} (hw : SvState.lookup st "w" = some vw) (hww : vw.width = N + 1)
    (hkw : ∀ k, k < N + 1 → KnownBit st "w" k) :
    SvState.lookup st "w" = some (LVec.ofBitVec (if c0 = true then x.concat false else BitVec.cons true x)) := by
  subst hW
  have hc0 : st.boolAt "cin" 0 = c0 := by
    have := SvState.boolAt_ofBitVec hCi (i := 0) (by simp)
    simpa using this
  rw [SvState.lookup_eq_ofBitVec_bv hw hww hkw] at hw
  rw [hw]
  congr 2
  cases c0
  · have ew' : ∀ k, k < W + 1 → st.boolAt "w" k = if k < W then st.boolAt "a" k else true := by
      intro k hk
      rw [ew k hk]
      simp only [hc0, Bool.false_eq_true, if_false]
      by_cases h : k < W
      · simp [h]
      · simp only [h, if_false]
        exact boolAt_one1 (by omega)
    rw [XF.bv_congr_lt ew', bv_cons_true, bv_of_lookup hA]
    simp
  · have ew' : ∀ k, k < W + 1 → st.boolAt "w" k = if k = 0 then false else st.boolAt "a" (k - 1) := by
      intro k hk
      rw [ew k hk]
      simp [hc0]
    rw [XF.bv_congr_lt ew', bv_concat_false, bv_of_lookup hA]
    simp

/-- **`e = ({a, b} == {b, a})`**: two concatenations compared, `BitVec` append on both sides. -/
theorem cat_add_e_final {W N : Nat} (hW : W = N) {st : SvState} {x y : BitVec N}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (ee : st.boolAt "e" 0 =
      XF.eqv (W + W) (fun x => if x < W then st.boolAt "b" x else st.boolAt "a" (x - W))
        fun x => if x < W then st.boolAt "a" x else st.boolAt "b" (x - W)) :
    st.boolAt "e" 0 = decide (x ++ y = y ++ x) := by
  subst hW
  rw [ee]
  have h : XF.eqv (W + W) (fun x => if x < W then st.boolAt "b" x else st.boolAt "a" (x - W))
      (fun x => if x < W then st.boolAt "a" x else st.boolAt "b" (x - W)) =
      decide (XF.bv (W + W) (fun x => if x < W then st.boolAt "b" x else st.boolAt "a" (x - W)) =
        XF.bv (W + W) (fun x => if x < W then st.boolAt "a" x else st.boolAt "b" (x - W))) := by
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact (LVec.eqv_iff_bv _ _).symm
  rw [h, XF.bv_cat2, XF.bv_cat2, bv_of_lookup hA, bv_of_lookup hB]

/-- **Concatenations in `+`, `?:` and `==`, every `N ≥ 1`.** -/
theorem cat_add_correct (N : Nat) (hN : 1 ≤ N) :
    cat_add.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
        SvState.lookup st "s" = some (LVec.ofBitVec
          (x.setWidth (N + 1) + y.setWidth (N + 1) + (BitVec.ofBool ci).setWidth (N + 1))) ∧
        SvState.lookup st "t" = some (LVec.ofBitVec (x.setWidth (N + 2) + (y.concat false).setWidth (N + 2))) ∧
        SvState.lookup st "w" = some (LVec.ofBitVec (if ci = true then x.concat false else BitVec.cons true x)) ∧
        SvState.lookup st "e" = some (LVec.ofBitVec (BitVec.ofBool (decide (x ++ y = y ++ x)))) := by
  have hc : CombDesign (cat_add.sem N) := by
    sv_structure
    all_goals (first | (intros; omega) | (intros; simp [LVec.width]; omega))
  have ha : Acyclic (cat_add.sem N) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (first | (intros; omega) | (intros; simp [LVec.width]; omega))
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y ci hA hB hCi
  sv_equations
  · obtain ⟨⟨vs, hvs, hvsw⟩, -⟩ := known_s_1 0 (by omega)
    obtain ⟨⟨vt, hvt, hvtw⟩, -⟩ := known_t_1 0 (by omega)
    obtain ⟨⟨vw, hvw, hvww⟩, -⟩ := known_w_1 0 (by omega)
    obtain ⟨⟨ve, hve, hvew⟩, hke⟩ := known_e_1
    refine ⟨cat_add_s_final (by omega) hA hB hCi eq_s_1 hvs hvsw (fun k hk => (known_s_1 k hk).2),
      cat_add_t_final (by omega) (by omega) hA hB eq_t_1 hvt hvtw (fun k hk => (known_t_1 k hk).2),
      cat_add_w_final (by omega) hA hCi eq_w_1 hvw hvww (fun k hk => (known_w_1 k hk).2), ?_⟩
    exact bit1_of_lookup hve hvew hke (cat_add_e_final (by omega) hA hB eq_e_1)
  all_goals first
    | (intros; omega)
    | (intros; simp [LVec.width]; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hCi ?_; omega)

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.add_same_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms add_same_correct

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.add_wide_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms add_wide_correct

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.sub_wide_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms sub_wide_correct

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.addw_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms addw_correct

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.addp_settles' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms addp_settles

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.cmp_same_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cmp_same_correct

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.trunc_inc_y1_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms trunc_inc_y1_final

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.shl_n_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shl_n_correct

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.shr_n_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shr_n_correct

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.shl_wide_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shl_wide_correct

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.onehot_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms onehot_correct

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.shl_const_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shl_const_correct

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.shl_n_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shl_n_final

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.onehot_final' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms onehot_final

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.cat_add_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cat_add_correct

/-! ## Rows of a two-dimensional packed array and constant part selects (WP-B2 gate 4a) -/

/-- **A chain of inverted rows** (`row_chain`, `row_chain_lp`, `row_chain_lit`): row `0` is `x`, row `i + 1` is the
inversion of row `i`, `y` is row `R`; so `y` is `x` for an even number of rows and `~~~x` for an odd one. The row width is
`C` and the stride of the row-major offset `rmN` is the integer `Wi` (the printed form of a parameter, a localparam
expression or a literal); `Ri` is the printed index of the last row. -/
theorem row_chain_gen {C R : Nat} {Wi Ri : Int} (hW : Wi = (C : Int)) (hR : Ri = (R : Int)) {st : SvState}
    {x : BitVec C} (hA : SvState.lookup st "x" = some (LVec.ofBitVec x))
    (e0 : ∀ k, k < C → st.boolAt "r" k = st.boolAt "x" k)
    (es : ∀ i, i < R → ∀ k, k < C →
      st.boolAt "r" (rmN Wi ((i : Int) + 1) 0 + k) = !st.boolAt "r" (rmN Wi (i : Int) 0 + k))
    (ey : ∀ k, k < C → st.boolAt "y" k = st.boolAt "r" (rmN Wi Ri 0 + k))
    {vy : LVec} (hy : SvState.lookup st "y" = some vy) (hyw : vy.width = C)
    (hky : ∀ k, k < C → KnownBit st "y" k) :
    SvState.lookup st "y" = some (LVec.ofBitVec (if R % 2 = 0 then x else ~~~x)) := by
  subst hW hR
  have hrow : ∀ i, i ≤ R → ∀ k, k < C → st.boolAt "r" (rmN (C : Int) (i : Int) 0 + k) =
      (if i % 2 = 0 then x.getLsbD k else !x.getLsbD k) := by
    intro i
    induction i with
    | zero =>
        intro _ k hk
        have e : ((0 : Nat) : Int) = 0 := rfl
        rw [e, rmN_zero_zero_add, e0 k hk, SvState.boolAt_ofBitVec hA hk]
        simp
    | succ j ih =>
        intro hj k hk
        have h1 := es j (by omega) k hk
        have h2 := ih (by omega) k hk
        have e : ((j + 1 : Nat) : Int) = (j : Int) + 1 := by omega
        rw [e, h1, h2]
        by_cases hp : j % 2 = 0
        · have : ¬ (j + 1) % 2 = 0 := by omega
          simp [hp, this]
        · have : (j + 1) % 2 = 0 := by omega
          simp [hp, this]
  have hxy : XF.bv C (st.boolAt "y") = (if R % 2 = 0 then x else ~~~x) := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    rw [XF.getLsbD_bv hk, ey k hk, hrow R (Nat.le_refl R) k hk]
    by_cases hp : R % 2 = 0
    · simp [hp]
    · simp [hp, hk]
  rw [SvState.lookup_eq_ofBitVec_bv hy hyw hky] at hy
  rw [hy, hxy]

/-- **A chain of rows over parameter dimensions, every `N ≥ 1`** (`logic [N:0][N-1:0] r`, `r[i + 1] = ~r[i]`: the legacy
`BitSel` over a two-dimensional base is a whole row). -/
theorem row_chain_correct (N : Nat) (hN : 1 ≤ N) :
    row_chain.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x : BitVec N), SvState.lookup st "x" = some (LVec.ofBitVec x) →
        SvState.lookup st "y" = some (LVec.ofBitVec (if N % 2 = 0 then x else ~~~x)) := by
  have hc : CombDesign (row_chain.sem N) := by
    sv_structure
    all_goals (intros; sv_rowmajor; omega)
  have ha : Acyclic (row_chain.sem N) := by
    sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
    all_goals (intros; sv_rowmajor; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x hA
  sv_equations
  · obtain ⟨⟨vy, hvy, hvyw⟩, -⟩ := known_y_plain_1 0 (by omega)
    exact row_chain_gen (by rfl) (by rfl) hA (fun k hk => eq_r_plain_0 k hk)
      (fun i hi k hk => eq_r_g_0 i hi k hk) (fun k hk => eq_y_plain_1 k (by omega)) hvy (by omega)
      (fun k hk => (known_y_plain_1 k (by omega)).2)
  case cover_1 =>
    intro k hk
    right
    refine ⟨N - 1, by omega, ?_⟩
    have e : (((N - 1 : Nat) : Int) + 1) = (N : Int) := by omega
    rw [e]
    omega
  case cover_2 =>
    intro i hi0 hiN k hk
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

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.row_chain_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms row_chain_correct

/-- **The same chain over LOCALPARAM dimensions, rows `2N` bits wide** (`logic [R-1:0][C-1:0] r` with `R = N + 1`,
`C = 2 * N`). -/
theorem row_chain_lp_correct (N : Nat) (hN : 1 ≤ N) :
    row_chain_lp.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x : BitVec (2 * N)), SvState.lookup st "x" = some (LVec.ofBitVec x) →
        SvState.lookup st "y" = some (LVec.ofBitVec (if N % 2 = 0 then x else ~~~x)) := by
  have hc : CombDesign (row_chain_lp.sem N) := by
    sv_structure
    all_goals (intros; sv_rowmajor; omega)
  have ha : Acyclic (row_chain_lp.sem N) := by
    sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
    all_goals (intros; sv_rowmajor; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x hA
  sv_equations
  · obtain ⟨⟨vy, hvy, hvyw⟩, -⟩ := known_y_plain_1 0 (by omega)
    exact row_chain_gen (by omega) (by rfl) hA (fun k hk => eq_r_plain_0 k (by omega))
      (fun i hi k hk => eq_r_g_0 i hi k (by omega)) (fun k hk => eq_y_plain_1 k (by omega)) hvy (by omega)
      (fun k hk => (known_y_plain_1 k (by omega)).2)
  case cover_1 =>
    intro k hk
    right
    refine ⟨N - 1, by omega, ?_⟩
    have e : (((N - 1 : Nat) : Int) + 1) = (N : Int) := by omega
    rw [e]
    omega
  case cover_2 =>
    intro i hi0 hiN k hk
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

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.row_chain_lp_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms row_chain_lp_correct

/-- **The same chain over LITERAL dimensions** (`logic [3:0][2:0] r`, three inversions): with a literal range every label is
the legacy `BitSel`, `r[0]` and `r[3]` included. -/
theorem row_chain_lit_correct :
    row_chain_lit.sem ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x : BitVec 3), SvState.lookup st "x" = some (LVec.ofBitVec x) →
        SvState.lookup st "y" = some (LVec.ofBitVec (~~~x)) := by
  have hc : CombDesign (row_chain_lit.sem) := by
    sv_structure
    all_goals (intros; sv_rowmajor; omega)
  have ha : Acyclic (row_chain_lit.sem) := by
    sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else 4) (fun _ _ i => i.toNat + 1))
    all_goals (intros; sv_rowmajor; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x hA
  sv_equations
  · obtain ⟨⟨vy, hvy, hvyw⟩, -⟩ := known_y_plain_1 0 (by omega)
    have h := row_chain_gen (C := 3) (R := 3) (by rfl) (by rfl) hA (fun k hk => eq_r_plain_0 k (by omega))
      (fun i hi k hk => eq_r_g_0 i (by omega) k (by omega)) (fun k hk => eq_y_plain_1 k (by omega)) hvy (by omega)
      (fun k hk => (known_y_plain_1 k (by omega)).2)
    simpa using h
  case cover_1 =>
    intro k hk
    right
    refine ⟨2, by omega, ?_⟩
    have e : (((2 : Nat) : Int) + 1) = 3 := by omega
    rw [e]
    omega
  case cover_2 =>
    intro i hi0 hiN k hk
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

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.row_chain_lit_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms row_chain_lit_correct

/-- **`ps_rot`, the rotation `{x[8:0], x[15:9]}`**: a concatenation of two literal-bound part selects is the rotation by 7. -/
theorem ps_rot_r_final {st : SvState} {x : BitVec 16}
    (hA : SvState.lookup st "x" = some (LVec.ofBitVec x))
    (er : ∀ k, k < 16 → st.boolAt "r" k = if k < 7 then st.boolAt "x" (9 + k) else st.boolAt "x" (k - 7))
    {vr : LVec} (hr : SvState.lookup st "r" = some vr) (hrw : vr.width = 16)
    (hkr : ∀ k, k < 16 → KnownBit st "r" k) :
    SvState.lookup st "r" = some (LVec.ofBitVec (x.rotateLeft 7)) := by
  rw [SvState.lookup_eq_ofBitVec_bv hr hrw hkr] at hr
  rw [hr]
  congr 2
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [XF.getLsbD_bv hk, er k hk, BitVec.getLsbD_rotateLeft]
  by_cases h7 : k < 7
  · simp [h7, SvState.boolAt_ofBitVec hA (by omega : 9 + k < 16)]
  · simp [h7, SvState.boolAt_ofBitVec hA (by omega : k - 7 < 16), hk]

/-- … the byte swap by two part-select TARGETS `sw[7:0] = x[15:8]`, `sw[15:8] = x[7:0]` is the rotation by 8, … -/
theorem ps_rot_sw_final {st : SvState} {x : BitVec 16}
    (hA : SvState.lookup st "x" = some (LVec.ofBitVec x))
    (e1 : ∀ k, k < 8 → st.boolAt "sw" k = st.boolAt "x" (8 + k))
    (e2 : ∀ k, k < 8 → st.boolAt "sw" (8 + k) = st.boolAt "x" k)
    {vs : LVec} (hs : SvState.lookup st "sw" = some vs) (hsw : vs.width = 16)
    (hks : ∀ k, k < 16 → KnownBit st "sw" k) :
    SvState.lookup st "sw" = some (LVec.ofBitVec (x.rotateLeft 8)) := by
  rw [SvState.lookup_eq_ofBitVec_bv hs hsw hks] at hs
  rw [hs]
  congr 2
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [XF.getLsbD_bv hk, BitVec.getLsbD_rotateLeft]
  by_cases h8 : k < 8
  · rw [e1 k h8]
    simp [h8, SvState.boolAt_ofBitVec hA (by omega : 8 + k < 16)]
  · have h := e2 (k - 8) (by omega)
    rw [show 8 + (k - 8) = k by omega] at h
    rw [h]
    simp [h8, SvState.boolAt_ofBitVec hA (by omega : k - 8 < 16), hk]

/-- … and the field `e = x[14:10]` is `extractLsb'`. -/
theorem ps_rot_e_final {st : SvState} {x : BitVec 16}
    (hA : SvState.lookup st "x" = some (LVec.ofBitVec x))
    (ee : ∀ k, k < 5 → st.boolAt "e" k = st.boolAt "x" (10 + k))
    {ve : LVec} (he : SvState.lookup st "e" = some ve) (hew : ve.width = 5)
    (hke : ∀ k, k < 5 → KnownBit st "e" k) :
    SvState.lookup st "e" = some (LVec.ofBitVec (x.extractLsb' 10 5)) := by
  rw [SvState.lookup_eq_ofBitVec_bv he hew hke] at he
  rw [he]
  congr 2
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [XF.getLsbD_bv hk, ee k hk, BitVec.getLsbD_extractLsb', SvState.boolAt_ofBitVec hA (by omega : 10 + k < 16)]
  simp [hk]

/-- **Literal-bound part selects**: the rotation, the byte swap and the field of `ps_rot`. -/
theorem ps_rot_correct :
    ps_rot.sem ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x : BitVec 16), SvState.lookup st "x" = some (LVec.ofBitVec x) →
        SvState.lookup st "r" = some (LVec.ofBitVec (x.rotateLeft 7)) ∧
        SvState.lookup st "sw" = some (LVec.ofBitVec (x.rotateLeft 8)) ∧
        SvState.lookup st "e" = some (LVec.ofBitVec (x.extractLsb' 10 5)) := by
  have hc : CombDesign (ps_rot.sem) := by
    sv_structure
    all_goals (intros; omega)
  have ha : Acyclic (ps_rot.sem) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x hA
  sv_equations
  · obtain ⟨⟨vr, hvr, hvrw⟩, -⟩ := known_r_plain_0 0 (by omega)
    obtain ⟨⟨vs, hvs, hvsw⟩, -⟩ := known_sw_plain_1 0 (by omega)
    obtain ⟨⟨ve, hve, hvew⟩, -⟩ := known_e_plain_3 0 (by omega)
    refine ⟨ps_rot_r_final hA (fun k hk => by simpa using eq_r_plain_0 k (by omega)) hvr (by omega)
        (fun k hk => (known_r_plain_0 k (by omega)).2),
      ps_rot_sw_final hA (fun k hk => by simpa using eq_sw_plain_1 k (by omega))
        (fun k hk => by simpa using eq_sw_plain_2 k (by omega)) hvs (by omega) (fun k hk => ?_),
      ps_rot_e_final hA (fun k hk => by simpa using eq_e_plain_3 k (by omega)) hve (by omega)
        (fun k hk => (known_e_plain_3 k (by omega)).2)⟩
    by_cases h8 : k < 8
    · exact (known_sw_plain_1 k (by omega)).2
    · have h := (known_sw_plain_2 (k - 8) (by omega)).2
      rwa [show Int.toNat 8 + (k - 8) = k by omega] at h
  all_goals first
    | (intros; omega)
    | (refine inKnown_ofBitVec hA ?_; omega)

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.ps_rot_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ps_rot_correct

/-- **Part selects with bounds affine in a genvar, read and written inside a generate loop** (`ps_gen`: `y[4*i+3:4*i] =
~x[4*i+3:4*i]`), every `N ≥ 1`: the four-bit windows tile `y`. -/
theorem ps_gen_final {N : Nat} {st : SvState} {x : BitVec (4 * N)}
    (hA : SvState.lookup st "x" = some (LVec.ofBitVec x))
    (ey : ∀ i, i < N → ∀ k, k < 4 → st.boolAt "y" (4 * i + k) = !st.boolAt "x" (4 * i + k))
    {vy : LVec} (hy : SvState.lookup st "y" = some vy) (hyw : vy.width = 4 * N)
    (hky : ∀ k, k < 4 * N → KnownBit st "y" k) :
    SvState.lookup st "y" = some (LVec.ofBitVec (~~~x)) := by
  rw [SvState.lookup_eq_ofBitVec_bv hy hyw hky] at hy
  rw [hy]
  congr 2
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [XF.getLsbD_bv hk, BitVec.getLsbD_not]
  have h := ey (k / 4) (by omega) (k % 4) (by omega)
  rw [show 4 * (k / 4) + k % 4 = k by omega] at h
  rw [h, SvState.boolAt_ofBitVec hA hk]
  simp [hk]

theorem ps_gen_correct (N : Nat) (hN : 1 ≤ N) :
    ps_gen.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x : BitVec (4 * N)), SvState.lookup st "x" = some (LVec.ofBitVec x) →
        SvState.lookup st "y" = some (LVec.ofBitVec (~~~x)) := by
  have hc : CombDesign (ps_gen.sem N) := by
    sv_structure
    all_goals (intros; omega)
  have ha : Acyclic (ps_gen.sem N) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x hA
  sv_equations
  · obtain ⟨⟨vy, hvy, hvyw⟩, -⟩ := known_y_g_0 0 (by omega) 0 (by omega)
    refine ps_gen_final hA (fun i hi k hk => ?_) hvy (by omega) (fun k hk => ?_)
    · have h := eq_y_g_0 i hi k (by omega)
      rwa [show (4 * (i : Int)).toNat = 4 * i by omega] at h
    · have h := (known_y_g_0 (k / 4) (by omega) (k % 4) (by omega)).2
      rwa [show (4 * ((k / 4 : Nat) : Int)).toNat + k % 4 = k by omega] at h
  all_goals first
    | (intros; omega)
    | (refine inKnown_ofBitVec hA ?_; omega)

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.ps_gen_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ps_gen_correct

/-! ## A genvar as the amount of a shift (WP-B2 gate 4b) -/

/-- The genvar `i < 2^32`, as the 32-bit literal an unsized constant is, reads back as `i`. -/
theorem toNat_ofInt32_nat {i : Nat} (hi : i < 2 ^ 32) : (BitVec.ofInt 32 (i : Int)).toNat = i := by
  rw [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi]

/-- **`shl_gen`**: row `i` of `pp` is `aw << i` (a genvar amount: the 32-bit literal of its value, `XF.constBit i 32`),
bit by bit; the amount is read modulo `2^32`, so `i < 2^32` is the one side condition. -/
theorem shl_gen_final {N : Nat} (hN32 : N ≤ 2 ^ 32) {st : SvState} {x : BitVec (2 * N)}
    (hA : SvState.lookup st "aw" = some (LVec.ofBitVec x))
    (e : ∀ i, i < N → ∀ k, k < 2 * N → st.boolAt "pp" (rmN (2 * (N : Int)) (i : Int) 0 + k) =
      XF.shlBits (XF.zext (2 * N) fun x => st.boolAt "aw" x) 32 (fun x => XF.constBit (i : Int) 32 x) k) :
    ∀ i, i < N → ∀ k, k < 2 * N → st.boolAt "pp" (i * (2 * N) + k) = (x <<< i).getLsbD k := by
  intro i hi k hk
  have hrm : rmN (2 * (N : Int)) (i : Int) 0 = i * (2 * N) := by
    have h1 : (2 * (N : Int)).toNat = 2 * N := by omega
    simp [rmN, h1]
  have h := e i hi k hk
  rw [hrm] at h
  rw [h]
  have hs := XF.bv_shlBits (w := 2 * N) (wl := 2 * N) (wr := 32) (fun x => st.boolAt "aw" x)
    (fun x => XF.constBit (i : Int) 32 x)
  rw [XF.bv_constBit, toNat_ofInt32_nat (by omega), bv_of_lookup hA, BitVec.setWidth_eq] at hs
  have := congrArg (fun v => v.getLsbD k) hs
  rw [XF.getLsbD_bv hk] at this
  exact this

/-- **Every row of the shifted array, every `N ≥ 1` (up to `2^32` rows).** -/
theorem shl_gen_correct (N : Nat) (hN : 1 ≤ N) (hN32 : N ≤ 2 ^ 32) :
    shl_gen.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x : BitVec (2 * N)), SvState.lookup st "aw" = some (LVec.ofBitVec x) →
        ∀ i, i < N → ∀ k, k < 2 * N →
          st.boolAt "pp" (i * (2 * N) + k) = (x <<< i).getLsbD k ∧ KnownBit st "pp" (i * (2 * N) + k) := by
  have hc : CombDesign (shl_gen.sem N) := by
    sv_structure
    all_goals (intros; sv_rowmajor; omega)
  have ha : Acyclic (shl_gen.sem N) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; sv_rowmajor; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x hA
  sv_equations
  · intro i hi k hk
    have hW : (2 * (N : Int) + -1).natAbs + 1 = 2 * N := by omega
    have hrm : rmN (2 * (N : Int)) (i : Int) 0 = i * (2 * N) := by
      have h1 : (2 * (N : Int)).toNat = 2 * N := by omega
      simp [rmN, h1]
    refine ⟨shl_gen_final hN32 hA (fun i hi k hk => ?_) i hi k hk, ?_⟩
    · have h := eq_pp_g_0 i hi k (by omega)
      rwa [hW] at h
    · have h := (known_pp_g_0 i hi k (by omega)).2
      rwa [hrm] at h
  all_goals first
    | (intros; omega)
    | (refine inKnown_ofBitVec hA ?_; omega)

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.shl_gen_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms shl_gen_correct

/-! ## Replication (WP-B2 gate 4c) -/

/-- **`repl_pad`**: `{ {K{1'b0}}, x }` is the zero extension of `x` (the replicated literal is the high part). -/
theorem repl_pad_final {N K : Nat} {st : SvState} {x : BitVec N}
    (hA : SvState.lookup st "x" = some (LVec.ofBitVec x))
    (e : ∀ k, k < N + K → st.boolAt "y" k = if k < N then st.boolAt "x" k else false)
    {vy : LVec} (hy : SvState.lookup st "y" = some vy) (hyw : vy.width = N + K)
    (hk : ∀ k, k < N + K → KnownBit st "y" k) :
    SvState.lookup st "y" = some (LVec.ofBitVec (x.setWidth (N + K))) := by
  rw [SvState.lookup_eq_ofBitVec_bv hy hyw hk] at hy
  rw [hy]
  congr 2
  apply BitVec.eq_of_getLsbD_eq
  intro k hk'
  rw [XF.getLsbD_bv hk', e k hk', BitVec.getLsbD_setWidth]
  by_cases h : k < N
  · simp [h, SvState.boolAt_ofBitVec hA h, hk']
  · simp [h, hk', BitVec.getLsbD_of_ge x k (by omega)]

/-- **Zero padding, every `N ≥ 1` and every `K`** (`K = 0` is the empty replication). -/
theorem repl_pad_correct (N K : Nat) (hN : 1 ≤ N) :
    repl_pad.sem N K ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x : BitVec N), SvState.lookup st "x" = some (LVec.ofBitVec x) →
        SvState.lookup st "y" = some (LVec.ofBitVec (x.setWidth (N + K))) := by
  have hc : CombDesign (repl_pad.sem N K) := by
    sv_structure
    all_goals (intros; omega)
  have ha : Acyclic (repl_pad.sem N K) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x hA
  sv_equations
  · obtain ⟨⟨vy, hvy, hvyw⟩, -⟩ := known_y_plain_0 0 (by omega)
    refine repl_pad_final hA (fun k hk => ?_) hvy (by omega) (fun k hk => (known_y_plain_0 k (by omega)).2)
    have h := eq_y_plain_0 k (by omega)
    rwa [show ((N : Int) + -1).natAbs + 1 = N by omega] at h
  all_goals first
    | (intros; omega)
    | (refine inKnown_ofBitVec hA ?_; omega)

/-- **`repl_mask`**: row `i` of the partial-product array, `a & {N{b[i]}}`, is `a` when bit `i` of `b` is set and zero
otherwise (the replicated operand is ONE bit select: every bit of the mask is `b[i]`). -/
theorem repl_mask_final {N : Nat} {st : SvState} {a b : BitVec N}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec a))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec b))
    (e : ∀ i, i < N → ∀ k, k < N →
      st.boolAt "pp" (rmN (N : Int) (i : Int) 0 + k) = (st.boolAt "a" k && st.boolAt "b" (i + k % 1))) :
    ∀ i, i < N → ∀ k, k < N → st.boolAt "pp" (i * N + k) = (if b.getLsbD i then a else 0#N).getLsbD k := by
  intro i hi k hk
  have hrm : rmN (N : Int) (i : Int) 0 = i * N := by simp [rmN]
  have h := e i hi k hk
  rw [hrm] at h
  rw [h, Nat.mod_one, Nat.add_zero, SvState.boolAt_ofBitVec hA hk, SvState.boolAt_ofBitVec hB hi]
  cases hb : b.getLsbD i <;> simp [hb]

/-- **The AND mask of a partial product, every `N ≥ 1`.** -/
theorem repl_mask_correct (N : Nat) (hN : 1 ≤ N) :
    repl_mask.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (a b : BitVec N), SvState.lookup st "a" = some (LVec.ofBitVec a) →
        SvState.lookup st "b" = some (LVec.ofBitVec b) →
          ∀ i, i < N → ∀ k, k < N →
            st.boolAt "pp" (i * N + k) = (if b.getLsbD i then a else 0#N).getLsbD k ∧
              KnownBit st "pp" (i * N + k) := by
  have hc : CombDesign (repl_mask.sem N) := by
    sv_structure
    all_goals (intros; sv_rowmajor; omega)
  have ha : Acyclic (repl_mask.sem N) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; sv_rowmajor; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro a b hA hB
  sv_equations
  · intro i hi k hk
    have hrm : rmN (N : Int) (i : Int) 0 = i * N := by simp [rmN]
    refine ⟨repl_mask_final hA hB (fun i hi k hk => eq_pp_g_0 i hi k hk) i hi k hk, ?_⟩
    have h := (known_pp_g_0 i hi k hk).2
    rwa [hrm] at h
  all_goals first
    | (intros; omega)
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)

/-- **`repl_bits`, `y = {4{x[1:0]}}`**: a replicated part select with a literal count is `BitVec.replicate` of the field
(the glue is core's `BitVec.getLsbD_replicate`). -/
theorem repl_bits_y_final {st : SvState} {x : BitVec 8}
    (hA : SvState.lookup st "x" = some (LVec.ofBitVec x))
    (e : ∀ k, k < 8 → st.boolAt "y" k = st.boolAt "x" (k % 2))
    {vy : LVec} (hy : SvState.lookup st "y" = some vy) (hyw : vy.width = 8)
    (hk : ∀ k, k < 8 → KnownBit st "y" k) :
    SvState.lookup st "y" = some (LVec.ofBitVec (BitVec.replicate 4 (x.extractLsb' 0 2))) := by
  rw [SvState.lookup_eq_ofBitVec_bv hy hyw hk] at hy
  rw [hy]
  congr 2
  apply BitVec.eq_of_getLsbD_eq
  intro k hk'
  rw [XF.getLsbD_bv hk', e k hk', BitVec.getLsbD_replicate, BitVec.getLsbD_extractLsb',
    SvState.boolAt_ofBitVec hA (by omega : k % 2 < 8)]
  have h2 : k % 2 < 2 := Nat.mod_lt _ (by omega)
  simp [h2, hk']

/-- **Replications with literal counts.** -/
theorem repl_bits_correct :
    repl_bits.sem ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x : BitVec 8), SvState.lookup st "x" = some (LVec.ofBitVec x) →
        SvState.lookup st "y" = some (LVec.ofBitVec (BitVec.replicate 4 (x.extractLsb' 0 2))) := by
  have hc : CombDesign (repl_bits.sem) := by
    sv_structure
    all_goals (intros; omega)
  have ha : Acyclic (repl_bits.sem) := by
    sv_structure (rank := rippleRank (fun _ => 0) (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x hA
  sv_equations
  · obtain ⟨⟨vy, hvy, hvyw⟩, -⟩ := known_y_plain_0 0 (by omega)
    exact repl_bits_y_final hA (fun k hk => by simpa using eq_y_plain_0 k (by omega)) hvy (by simpa using hvyw)
      (fun k hk => (known_y_plain_0 k (by omega)).2)
  all_goals first
    | (intros; omega)
    | (refine inKnown_ofBitVec hA ?_; omega)

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.repl_pad_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms repl_pad_correct

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.repl_mask_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms repl_mask_correct

/-- info: 'Examples.«system-verilog».comb_word.comb_proof.repl_bits_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms repl_bits_correct

end Examples.«system-verilog».comb_word.comb_proof
