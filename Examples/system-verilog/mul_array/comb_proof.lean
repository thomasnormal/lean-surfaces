import Examples.«system-verilog».mul_array.comb_view
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

/-!
# The array multiplier, for every `N ≥ 1`, by `sv_structure` + `sv_equations`

`mul_n.sv` (`Examples/system-verilog/mul_array`, byte-identical to `svgolf/tasks/mul/reference/mul_n.sv`)
is proved to compute the full product, for EVERY `N ≥ 1`, from

* `sv_structure` (lane M, `comb_view.lean`): `CombDesign` and `Acyclic` of `mul_n.sem N`
  (`mul_comb`, `mul_acyclic`: 2 + 2 tactic lines);
* `sv_equations`: the settled-state equations of the 2-D netlist, derived from the real semantics —
  one named hypothesis per assign (`eq_pp_g_pp_j_0`, `eq_t_g_bit_0`, `eq_s_g_bit_1`, `eq_c_g_bit_2`,
  …), over `Bool`, with the SV's gate structure; the row stride hides inside `rmN W i j`;
* the plain-Lean consumer half `LeanModels/Sv/CombLib.lean` (`MulNetlistView`, `ideal_mul_view`: the
  ripple-row lemma and the row induction).

What the player writes: `mul_final` (the bridge from the equations to the port value, one line per
field of `MulNetlistView`) and the closers of the obligations `sv_equations` returns. The
one-bit/1-D obligations close by `intros; omega`/`sv_cover`; the six COVERAGE goals of the 2-D reads
(`cover_2`, `cover_4`–`cover_8`: "the cell this assign reads is written by some assign") are closed
BY HAND below, each by naming the writer (`refine ⟨i.toNat, …⟩`) and one `cov_leaf`: this is the
line of the automation (`sv_cover` closes `cover_1`, `cover_3` and all the 1-D goals of the adder,
but its witness search is too slow for the nested 2-D ones).
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq
open Examples.«system-verilog».mul_array.gen
open Examples.«system-verilog».mul_array.comb_view

namespace Examples.«system-verilog».mul_array.comb_proof

/-- The leaf of a coverage proof: witnesses cast back, row-major comparisons lexicographic, `omega`. -/
macro "cov_leaf" : tactic =>
  `(tactic| first
    | omega
    | ((try simp (disch := omega) only [Int.toNat_of_nonneg, LeanModels.Sv.CombView.rmN_add_col,
        LeanModels.Sv.CombView.rmN_lt_iff, LeanModels.Sv.CombView.rmN_le_iff, Int.toNat_natCast,
        Int.natCast_zero, Int.natCast_one, true_and, and_true, eq_self] at *); first | done | omega))

/-- **The player's arithmetic.** From the equations of the netlist (as `sv_equations` states them)
and the knownness of `p`: the port value `p = a * b`. -/
theorem mul_final {N : Nat} (hN : 1 ≤ N) {st : SvState} {x y : BitVec N}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (e_s0 : ∀ k, k < N + 1 → st.boolAt "s" k = if k < N then st.boolAt "pp" k else false)
    (e_c0 : ∀ k, k < N + 1 → st.boolAt "c" k = false)
    (e_t0 : ∀ k, k < N → st.boolAt "t" k = false)
    (e_ph : ∀ k, k < (2 * (N : Int) + -1 - N + 1).toNat →
      st.boolAt "p" (N + k) = st.boolAt "s" (rmN ((N : Int) + 1) ((N : Int) + -1) 1 + k))
    (e_pp : ∀ i, i < N → ∀ j, j < N →
      st.boolAt "pp" (rmN (N : Int) i j) = (st.boolAt "a" j && st.boolAt "b" i))
    (e_ci0 : ∀ i : Nat, 1 ≤ (i : Int) → i < N → st.boolAt "c" (rmN ((N : Int) + 1) i 0) = false)
    (e_t : ∀ i : Nat, 1 ≤ (i : Int) → i < N → ∀ j, j < N →
      st.boolAt "t" (rmN (N : Int) i j) =
        (st.boolAt "s" (rmN ((N : Int) + 1) ((i : Int) + -1) ((j : Int) + 1)) ^^
          st.boolAt "pp" (rmN (N : Int) i j)))
    (e_s : ∀ i : Nat, 1 ≤ (i : Int) → i < N → ∀ j, j < N →
      st.boolAt "s" (rmN ((N : Int) + 1) i j) =
        (st.boolAt "t" (rmN (N : Int) i j) ^^ st.boolAt "c" (rmN ((N : Int) + 1) i j)))
    (e_c : ∀ i : Nat, 1 ≤ (i : Int) → i < N → ∀ j, j < N →
      st.boolAt "c" (rmN ((N : Int) + 1) i ((j : Int) + 1)) =
        (st.boolAt "s" (rmN ((N : Int) + 1) ((i : Int) + -1) ((j : Int) + 1)) &&
            st.boolAt "pp" (rmN (N : Int) i j) ||
          st.boolAt "c" (rmN ((N : Int) + 1) i j) && st.boolAt "t" (rmN (N : Int) i j)))
    (e_stop : ∀ i : Nat, 1 ≤ (i : Int) → i < N →
      st.boolAt "s" (rmN ((N : Int) + 1) i N) = st.boolAt "c" (rmN ((N : Int) + 1) i N))
    (e_pl : ∀ i, i < N → st.boolAt "p" i = st.boolAt "s" (rmN ((N : Int) + 1) i 0))
    {vp : LVec} (hp : SvState.lookup st "p" = some vp) (hpw : vp.width = 2 * N)
    (hkp : ∀ k, k < 2 * N → KnownBit st "p" k) :
    SvState.lookup st "p" = some (LVec.ofBitVec (BitVec.ofNat (2 * N) (x.toNat * y.toNat))) := by
  have hvp := SvState.lookup_eq_ofBitVec_bv hp hpw hkp
  rw [hvp] at hp
  have ba : ∀ i, i < N → st.boolAt "a" i = x.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hA hi
  have bb : ∀ i, i < N → st.boolAt "b" i = y.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hB hi
  have hview : MulNetlistView N x y (XF.bv (2 * N) (st.boolAt "p"))
      (fun i j => st.boolAt "pp" (rmN (N : Int) i j))
      (fun i j => st.boolAt "t" (rmN (N : Int) i j))
      (fun i j => st.boolAt "s" (rmN ((N : Int) + 1) i j))
      (fun i j => st.boolAt "c" (rmN ((N : Int) + 1) i j)) := by
    have hcs : ∀ i : Nat, 1 ≤ i → ((i - 1 : Nat) : Int) = (i : Int) + -1 := fun i hi => by omega
    have hcj : ∀ j : Nat, ((j + 1 : Nat) : Int) = (j : Int) + 1 := fun j => by omega
    refine
      { pp_def := fun i hi j hj => ?_, s0 := fun j hj => ?_, s0_top := ?_, c0 := fun j hj => ?_,
        t0 := fun j hj => ?_, ci0 := fun i h1 h2 => ?_, t_def := fun i h1 h2 j hj => ?_,
        s_def := fun i h1 h2 j hj => ?_, c_def := fun i h1 h2 j hj => ?_,
        s_top := fun i h1 h2 => ?_, p_low := fun i hi => ?_, p_high := fun j hj => ?_ }
    · show st.boolAt "pp" (rmN (N : Int) i j) = (x.getLsbD j && y.getLsbD i)
      rw [e_pp i hi j hj, ba j hj, bb i hi]
    · simp only [Int.natCast_zero, rmN_zero_row, Int.toNat_natCast]
      rw [e_s0 j (by omega), if_pos hj]
    · simp only [Int.natCast_zero, rmN_zero_row, Int.toNat_natCast]
      rw [e_s0 N (by omega)]
      simp
    · simp only [Int.natCast_zero, rmN_zero_row, Int.toNat_natCast]
      exact e_c0 j (by omega)
    · simp only [Int.natCast_zero, rmN_zero_row, Int.toNat_natCast]
      exact e_t0 j hj
    · simp only [Int.natCast_zero]
      exact e_ci0 i (by omega) h2
    · show st.boolAt "t" (rmN (N : Int) i j) =
        (st.boolAt "s" (rmN ((N : Int) + 1) ((i - 1 : Nat) : Int) ((j + 1 : Nat) : Int)) ^^
          st.boolAt "pp" (rmN (N : Int) i j))
      rw [hcs i h1, hcj j]
      exact e_t i (by omega) h2 j hj
    · exact e_s i (by omega) h2 j hj
    · show st.boolAt "c" (rmN ((N : Int) + 1) i ((j + 1 : Nat) : Int)) =
        (st.boolAt "s" (rmN ((N : Int) + 1) ((i - 1 : Nat) : Int) ((j + 1 : Nat) : Int)) &&
            st.boolAt "pp" (rmN (N : Int) i j) ||
          st.boolAt "c" (rmN ((N : Int) + 1) i j) && st.boolAt "t" (rmN (N : Int) i j))
      rw [hcs i h1, hcj j]
      exact e_c i (by omega) h2 j hj
    · exact e_stop i (by omega) h2
    · show (XF.bv (2 * N) (st.boolAt "p")).getLsbD i =
        st.boolAt "s" (rmN ((N : Int) + 1) i ((0 : Nat) : Int))
      rw [XF.getLsbD_bv (by omega), e_pl i hi]
      simp only [Int.natCast_zero]
    · show (XF.bv (2 * N) (st.boolAt "p")).getLsbD (N + j) =
        st.boolAt "s" (rmN ((N : Int) + 1) ((N - 1 : Nat) : Int) ((j + 1 : Nat) : Int))
      rw [XF.getLsbD_bv (by omega), e_ph j (by omega), rmN_add_col j (by omega), hcs N hN, hcj j,
        Int.add_comm 1 (j : Int)]
  rw [hp]
  congr 2
  exact ideal_mul_view hN hview

set_option maxHeartbeats 2000000 in
/-- **Multiplier correctness, every `N ≥ 1`**: `p` is the full product `a * b` on `2N` bits. -/
theorem mul_correct (N : Nat) (hN : 1 ≤ N) :
    mul_n.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "p" =
          some (LVec.ofBitVec (BitVec.ofNat (2 * N) (x.toNat * y.toNat))) := by
  have hc := mul_comb N hN
  have ha := mul_acyclic N hN
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y hA hB
  sv_equations
  · obtain ⟨⟨vp, hvp, hvpw⟩, -⟩ := known_p_g_out_0 0 (by omega)
    refine mul_final hN hA hB eq_s_plain_0 eq_c_plain_1 eq_t_plain_2 eq_p_plain_3 eq_pp_g_pp_j_0
      eq_c_g_row_0 eq_t_g_bit_0 eq_s_g_bit_1 eq_c_g_bit_2 eq_s_g_row_2 eq_p_g_out_0 hvp (by omega) ?_
    intro k hk
    by_cases h : k < N
    · exact (known_p_g_out_0 k h).2
    · obtain ⟨j, rfl⟩ : ∃ j, k = N + j := ⟨k - N, by omega⟩
      exact (known_p_plain_3 j (by omega)).2
  case inputsKnown_1 => exact inKnown_ofBitVec hA (by omega)
  case inputsKnown_2 => exact inKnown_ofBitVec hB (by omega)
  -- coverage of the 2-D reads: name the writer
  case cover_2 =>
    intro k hk
    by_cases h1 : k + 1 < N
    · right; left
      refine ⟨N - 1, by omega, by omega, k + 1, h1, ?_⟩
      cov_leaf
    · by_cases h3 : N = 1
      · left; subst h3; cov_leaf
      · right; right
        refine ⟨N - 1, by omega, by omega, ?_⟩
        cov_leaf
  case cover_4 =>
    intro i hi1 hiN j hj0 hjN
    refine ⟨?_, ?_⟩
    · by_cases hA : i = 1
      · left; subst hA; cov_leaf
      · by_cases hB : j + 1 < N
        · right; left
          refine ⟨(i - 1).toNat, by omega, by omega, (j + 1).toNat, by omega, ?_⟩
          cov_leaf
        · right; right
          refine ⟨(i - 1).toNat, by omega, by omega, ?_⟩
          cov_leaf
    · refine ⟨i.toNat, by omega, j.toNat, by omega, ?_⟩
      cov_leaf
  case cover_5 =>
    intro i hi1 hiN j hj0 hjN
    refine ⟨?_, ?_⟩
    · right
      refine ⟨i.toNat, by omega, by omega, j.toNat, by omega, ?_⟩
      cov_leaf
    · by_cases hj : j = 0
      · right; left; subst hj
        refine ⟨i.toNat, by omega, by omega, ?_⟩
        cov_leaf
      · right; right
        refine ⟨i.toNat, by omega, by omega, (j - 1).toNat, by omega, ?_⟩
        cov_leaf
  case cover_6 =>
    intro i hi1 hiN j hj0 hjN
    refine ⟨?_, ?_, ?_, ?_⟩
    · by_cases hA : i = 1
      · left; subst hA; cov_leaf
      · by_cases hB : j + 1 < N
        · right; left
          refine ⟨(i - 1).toNat, by omega, by omega, (j + 1).toNat, by omega, ?_⟩
          cov_leaf
        · right; right
          refine ⟨(i - 1).toNat, by omega, by omega, ?_⟩
          cov_leaf
    · refine ⟨i.toNat, by omega, j.toNat, by omega, ?_⟩
      cov_leaf
    · by_cases hj : j = 0
      · right; left; subst hj
        refine ⟨i.toNat, by omega, by omega, ?_⟩
        cov_leaf
      · right; right
        refine ⟨i.toNat, by omega, by omega, (j - 1).toNat, by omega, ?_⟩
        cov_leaf
    · right
      refine ⟨i.toNat, by omega, by omega, j.toNat, by omega, ?_⟩
      cov_leaf
  case cover_7 =>
    intro i hi1 hiN
    right; right
    refine ⟨i.toNat, by omega, by omega, N - 1, by omega, ?_⟩
    cov_leaf
  case cover_8 =>
    intro i hi0 hiN
    by_cases h0 : i = 0
    · left; subst h0; cov_leaf
    · right; left
      refine ⟨i.toNat, by omega, by omega, 0, by omega, ?_⟩
      cov_leaf
  all_goals first | (intros; omega) | sv_cover

/-- info: 'Examples.«system-verilog».mul_array.comb_proof.mul_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms mul_correct

end Examples.«system-verilog».mul_array.comb_proof
