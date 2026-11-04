import Examples.«system-verilog».lp_add.gen
import Examples.«system-verilog».ripple_add.comb_proof
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombLib

/-!
# The ripple-carry adder with LOCALPARAMS, for every `N ≥ 1`, by `sv_structure` + `sv_equations`

`lp_add.sv` is `ripple_add.sv` with its sizes spelled through `localparam integer`s of `N` (see
`gen.lean`): the loop runs to `T = 2 * ((N + 1) / 2) - N % 2` and the carry vector is `[T:0]`. The
theorem is the ripple adder's (`ripple_add/comb_proof.lean`), and so is the whole arithmetic
(`ripple_final` is imported from there): the only new lines are the three places where a
localparam-sized bound meets the plain `N`, each one `omega` (`T = N`, from the definitions of `H` and
`R` as `omega` reads them: floor `/` and `%` by a literal, the truncating forms having been rewritten
under `hN` by the tactic).
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq
open Examples.«system-verilog».lp_add.gen
open Examples.«system-verilog».ripple_add.comb_proof (ripple_final)

namespace Examples.«system-verilog».lp_add.comb_proof

/-- The structure of `lp_add`: a combinational design (the proof is three declarations, one for the structure, one for
the rank and one for the settled equations: every declaration has its own heartbeat budget, and the whole proof had
needed 199 000 of the 200 000 default and carried a `maxHeartbeats` option for it). -/
theorem lp_comb (N : Nat) (hN : 1 ≤ N) : CombDesign (lp_add.sem N) := by
  sv_structure
  all_goals (intros; omega)

theorem lp_acyclic (N : Nat) (hN : 1 ≤ N) : Acyclic (lp_add.sem N) := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
  all_goals (intros; omega)

/-- The equations of `lp_add` in a settled state (the second half of `lp_correct`). The tactics' own `simp` and
`omega` carry the quotient and remainder of the localparam definitions. -/
theorem lp_settled (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (lp_add.sem N)) (ha : Acyclic (lp_add.sem N))
    (st : SvState) (heqs : CombEqs (lp_add.sem N) st) (hsh : StateShape (lp_add.sem N) st)
    (x y : BitVec N) (ci : Bool)
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hCi : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci))) :
    SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
    SvState.lookup st "cout" =
      some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) := by
  sv_equations
  · obtain ⟨⟨vs, hvs, hvsw⟩, -⟩ := known_s_g_bit_0 0 (by omega)
    obtain ⟨⟨vc, hvc, hvcw⟩, hkc⟩ := known_cout_plain_1
    exact ripple_final hN hA hB hCi eq_c_plain_0 (fun i hi => eq_c_g_bit_1 i (by omega))
      (fun i hi => eq_s_g_bit_0 i (by omega)) eq_cout_plain_1 hvs
      (by omega) (fun k hk => (known_s_g_bit_0 k (by omega)).2) hvc hvcw hkc
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hCi ?_; omega)

/-- **Ripple-adder correctness with localparams, every `N ≥ 1`.** -/
theorem lp_correct (N : Nat) (hN : 1 ≤ N) :
    lp_add.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
        SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
        SvState.lookup st "cout" =
          some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) := by
  have hc := lp_comb N hN
  have ha := lp_acyclic N hN
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y ci hA hB hCi
  exact lp_settled N hN hc ha st heqs hsh x y ci hA hB hCi

/-- info: 'Examples.«system-verilog».lp_add.comb_proof.lp_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms lp_correct

end Examples.«system-verilog».lp_add.comb_proof
