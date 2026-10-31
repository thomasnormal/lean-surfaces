import Examples.«system-verilog».comb_ops.gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

/-!
# The adder with `~` and `?:`, for every `N ≥ 1`, by `sv_structure` + `sv_equations` (WP-G S2)

`add_mux.sv` writes the carry cell as a conditional expression and the propagate and sum cells with `~`
(`e[i] = ~(a[i] ^ b[i])`, `c[i+1] = e[i] ? a[i] : c[i]`, `s[i] = ~(e[i] ^ c[i])`). The proof is the one of
`ripple_add/comb_proof.lean` with ONE different lemma: the equations are

    eq_e_1 : ∀ i, i < N → st.boolAt "e" i = !(st.boolAt "a" i ^^ st.boolAt "b" i)
    eq_c_2 : ∀ i, i < N → st.boolAt "c" (i + 1) = if st.boolAt "e" i = true then st.boolAt "a" i else st.boolAt "c" i
    eq_s_1 : ∀ i, i < N → st.boolAt "s" i = !(st.boolAt "e" i ^^ st.boolAt "c" i)

and `mux_final` turns them into the library structure `AddView` by a case split on three Booleans (the
carry cell is the majority; the sum cell is the parity). The rest is `ripple_final`'s.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq
open Examples.«system-verilog».comb_ops.gen

namespace Examples.«system-verilog».comb_ops.comb_proof

/-- **The player's arithmetic**: from the equations of the netlist and the knownness of `s` and `cout`: the
port values. -/
theorem mux_final {N : Nat} (hN : 1 ≤ N) {st : SvState} {x y : BitVec N} {ci : Bool}
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hCi : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)))
    (e0 : st.boolAt "c" 0 = st.boolAt "cin" 0)
    (ee : ∀ i, i < N → st.boolAt "e" i = !(st.boolAt "a" i ^^ st.boolAt "b" i))
    (estep : ∀ i, i < N → st.boolAt "c" (i + 1) =
      if st.boolAt "e" i = true then st.boolAt "a" i else st.boolAt "c" i)
    (esum : ∀ i, i < N → st.boolAt "s" i = !(st.boolAt "e" i ^^ st.boolAt "c" i))
    (eout : st.boolAt "cout" 0 = st.boolAt "c" N)
    {vs : LVec} (hs : SvState.lookup st "s" = some vs) (hsw : vs.width = N)
    (hks : ∀ k, k < N → KnownBit st "s" k)
    {vc : LVec} (hc : SvState.lookup st "cout" = some vc) (hcw : vc.width = 1)
    (hkc : KnownBit st "cout" 0) :
    SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
    SvState.lookup st "cout" =
      some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) := by
  have hvs := SvState.lookup_eq_ofBitVec_bv hs hsw hks
  have hvc := SvState.lookup_eq_ofBitVec_bv hc hcw (fun k hk => by
    obtain rfl : k = 0 := by omega
    exact hkc)
  rw [hvs] at hs
  rw [hvc] at hc
  have ba : ∀ i, i < N → st.boolAt "a" i = x.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hA hi
  have bb : ∀ i, i < N → st.boolAt "b" i = y.getLsbD i := fun i hi => SvState.boolAt_ofBitVec hB hi
  have bci : st.boolAt "cin" 0 = ci := by
    rw [SvState.boolAt_ofBitVec hCi (by omega)]; simp
  have hv : AddView N x y ci (fun i => st.boolAt "c" i) (XF.bv N (st.boolAt "s")).getLsbD
      (st.boolAt "cout" 0) := by
    refine ⟨by simpa [bci] using e0, fun i hi => ?_, fun i hi => ?_, by rw [eout]⟩
    · -- the carry cell: `e ? a : c` with `e = ~(a ^ b)` is the majority
      have h1 := estep i hi
      rw [ee i hi, ba i hi, bb i hi] at h1
      simp only [h1]
      generalize x.getLsbD i = a
      generalize y.getLsbD i = b
      generalize st.boolAt "c" i = c
      cases a <;> cases b <;> cases c <;> decide
    · -- the sum cell: `~(~(a ^ b) ^ c)` is the parity
      rw [XF.getLsbD_bv hi, esum i hi, ee i hi, ba i hi, bb i hi]
      generalize x.getLsbD i = a
      generalize y.getLsbD i = b
      generalize st.boolAt "c" i = c
      cases a <;> cases b <;> cases c <;> decide
  have hval := add_value hv
  rw [bfVal_bv] at hval
  obtain ⟨h1, h2⟩ := sum_split (XF.bv N (st.boolAt "s")).isLt hval.symm
  have hM : 0 < 2 ^ N := Nat.two_pow_pos N
  have hc1 : ci.toNat < 2 ^ N := by
    have : 2 ≤ 2 ^ N := Nat.pow_le_pow_right (n := 2) (by decide) hN
    have := Bool.toNat_le ci
    omega
  have hxb : XF.bv 1 (st.boolAt "cout") = BitVec.ofBool (st.boolAt "cout" 0) := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    obtain rfl : i = 0 := by omega
    rw [XF.getLsbD_bv hi]; simp
  refine ⟨?_, ?_⟩
  · rw [hs]
    congr 2
    apply BitVec.eq_of_toNat_eq
    rw [h1]
    simp only [BitVec.toNat_add, BitVec.toNat_setWidth, BitVec.toNat_ofBool,
      Nat.mod_eq_of_lt hc1, Nat.mod_add_mod]
  · rw [hxb] at hc
    rw [hc]
    congr 2
    have : st.boolAt "cout" 0 = decide (2 ^ N ≤ x.toNat + y.toNat + ci.toNat) := by
      cases hco : st.boolAt "cout" 0
      · rw [hco] at h2
        simp only [Bool.toNat_false] at h2
        have : x.toNat + y.toNat + ci.toNat < 2 ^ N := by
          have := (Nat.div_lt_iff_lt_mul hM).mp
            (by omega : (x.toNat + y.toNat + ci.toNat) / 2 ^ N < 1)
          omega
        simp [Nat.not_le.mpr this]
      · rw [hco] at h2
        simp only [Bool.toNat_true] at h2
        have := (Nat.le_div_iff_mul_le hM).mp
          (by omega : 1 ≤ (x.toNat + y.toNat + ci.toNat) / 2 ^ N)
        simp [show 2 ^ N ≤ x.toNat + y.toNat + ci.toNat by omega]
    rw [this]

/-- **Adder correctness, every `N ≥ 1`** (the statement of `ripple_add`'s `ripple_correct`). -/
theorem add_mux_correct (N : Nat) (hN : 1 ≤ N) :
    add_mux.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
        SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
        SvState.lookup st "cout" =
          some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) := by
  have hc : CombDesign (add_mux.sem N) := by
    sv_structure
    all_goals (intros; omega)
  have ha : Acyclic (add_mux.sem N) := by
    sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1)
      (fun _ pos i => if pos = 0 then 0 else i.toNat + 1))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y ci hA hB hCi
  sv_equations
  · obtain ⟨⟨vs, hvs, hvsw⟩, -⟩ := known_s_1 0 (by omega)
    obtain ⟨⟨vc, hvc, hvcw⟩, hkc⟩ := known_cout_1
    exact mux_final hN hA hB hCi eq_c_1 eq_e_1 eq_c_2 eq_s_1 eq_cout_1 hvs
      (by omega) (fun k hk => (known_s_1 k hk).2) hvc hvcw hkc
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hCi ?_; omega)

/-- info: 'Examples.«system-verilog».comb_ops.comb_proof.add_mux_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms add_mux_correct

end Examples.«system-verilog».comb_ops.comb_proof
