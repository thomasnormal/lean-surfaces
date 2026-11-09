import Examples.«system-verilog».comb_hier.gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombWordPins

/-!
# The two halves, for every even width, by `sv_structure` + `sv_equations`

`halves.sv` computes `y = a ^ b` with one leaf instance per half. `sv_structure` and `sv_equations` read the design through
its flat twin (`gen.lean`): the structure obligations are the twin's (the rank orders each half's connection, leaf and output
assignments), and the equations are those of the twin's eight sites, named after the flattened signals (`eq_lo_y_1` for the
leaf `lo`'s `y`, `eq_y_1`/`eq_y_2` for the two halves of the output).

* `halves_correct`: in every settled state at `W = 2 * K`, `y = a ^ b`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».comb_hier.gen

namespace Examples.«system-verilog».comb_hier.comb_proof

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

/-- **The two halves compute the XOR of the whole word**, at every even width `W = 2 * K` in the `int` range. -/
theorem halves_correct (K : Nat) (hK : 1 ≤ K) (hR : (2 * K : Int) < 2147483648) :
    halves.sem (2 * K) ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (u v : BitVec (2 * K)), SvState.lookup st "a" = some (LVec.ofBitVec u) →
        SvState.lookup st "b" = some (LVec.ofBitVec v) →
        SvState.lookup st "y" = some (LVec.ofBitVec (u ^^^ v)) := by
  obtain ⟨hc, ha⟩ : CombDesign (halves.sem (2 * K)) ∧ Acyclic (halves.sem (2 * K)) := by
    sv_structure (rank := rippleRank (fun p => if p % 4 = 2 then 2 else if p % 4 = 3 then 1 else 0)
      (fun _ _ _ => 0))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro u v hA hB
  sv_equations
  · -- the widths: each half is `K` bits, the word `2 * K`
    have e1 : ((↑(2 * K) : Int) / 2 + -1).natAbs + 1 = K := by omega
    have e2 : ((↑(2 * K) : Int) / 2 + -1 + 1).toNat = K := by omega
    have e3 : ((↑(2 * K) : Int) / 2).toNat = K := by omega
    have e4 : ((↑(2 * K) : Int) + -1 - ↑(2 * K) / 2 + 1).toNat = K := by omega
    have e5 : ((↑(2 * K) : Int) + -1).natAbs + 1 = 2 * K := by omega
    rw [e1] at eq_lo_a_1 eq_lo_b_1 eq_lo_y_1 eq_hi_a_1 eq_hi_b_1 eq_hi_y_1
    rw [e3] at eq_hi_a_1 eq_hi_b_1 eq_y_2 known_y_2
    rw [e2] at eq_y_1 known_y_1
    rw [e4] at eq_y_2 known_y_2
    rw [e5] at known_y_1 known_y_2
    have hk : ∀ k, k < 2 * K → (∃ w, SvState.lookup st "y" = some w ∧ w.width = 2 * K) ∧ KnownBit st "y" k := by
      intro k hk
      by_cases h : k < K
      · exact known_y_1 k h
      · have := known_y_2 (k - K) (by omega)
        rwa [Nat.add_sub_cancel' (by omega)] at this
    rw [lookup_bv hk (by omega)]
    congr 2
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [XF.getLsbD_bv hi, BitVec.getLsbD_xor]
    by_cases h : i < K
    · -- the low half, through the leaf `lo`
      rw [eq_y_1 i h, eq_lo_y_1 i h, eq_lo_a_1 i h, eq_lo_b_1 i h, SvState.boolAt_ofBitVec hA hi,
        SvState.boolAt_ofBitVec hB hi]
    · -- the high half, through the leaf `hi`
      obtain ⟨j, rfl⟩ : ∃ j, i = K + j := ⟨i - K, by omega⟩
      rw [eq_y_2 j (by omega), eq_hi_y_1 j (by omega), eq_hi_a_1 j (by omega), eq_hi_b_1 j (by omega),
        SvState.boolAt_ofBitVec hA hi, SvState.boolAt_ofBitVec hB hi]
  all_goals first
    | (intros; omega)
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)

/-- info: 'Examples.«system-verilog».comb_hier.comb_proof.halves_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms halves_correct

end Examples.«system-verilog».comb_hier.comb_proof
