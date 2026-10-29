import Examples.«system-verilog».ripple_add.comb_proof

/-!
# Negative tests for `sv_equations`: tampered adders

Three one-assign tamperings of `ripple_add.sv` (the envelopes in this directory are produced by the
extractor from the three `.sv` files next to them):

* `ripple_bad_gate.sv`   — the sum cell is `a[i] | b[i] ^ c[i]` (a wrong gate);
* `ripple_bad_carry.sv`  — the ripple runs DOWNWARDS (carry-in at `c[N]`, carry-out `c[0]`);
* `ripple_bad_offset.sv` — the sum cell reads `b[N-1-i]` (a wrong, in-range, slice offset).

For each: (1) `sv_structure` and `sv_equations` still run, and the equation they hand over for the
tampered assign IS the tampered one, verbatim (`*_eq` theorems: the producer reads the design it
is given, not the specification); (2) the final correctness proof — the very script that proves the
genuine adder (`comb_proof.ripple_correct`) — FAILS (`example … := by fail_if_success …`), because
the produced equations no longer have the shape `ripple_final` consumes. A CONTROL runs the same
wrapper on the genuine adder: the wrapper reports that the proof succeeded, i.e. the wrapper can
tell success from failure.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq LeanModels.Sv.CombLib
open Examples.«system-verilog».ripple_add.gen
open Examples.«system-verilog».ripple_add.comb_proof (ripple_final)

namespace Examples.«system-verilog».ripple_add.neg

load_design_sv2 bad_gate from "Examples/system-verilog/ripple_add/neg/ripple_bad_gate.sv.json"
load_design_sv2 bad_carry from "Examples/system-verilog/ripple_add/neg/ripple_bad_carry.sv.json"
load_design_sv2 bad_offset from "Examples/system-verilog/ripple_add/neg/ripple_bad_offset.sv.json"

-- The player's closers of the obligations (those of `comb_proof.ripple_correct`).
set_option hygiene false in
macro "ripple_obligations" : tactic =>
  `(tactic| all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hCi ?_; omega))

-- The final step of `comb_proof.ripple_correct`.
set_option hygiene false in
macro "ripple_close" : tactic =>
  `(tactic| (
    obtain ⟨⟨vs, hvs, hvsw⟩, -⟩ := known_s_g_bit_0 0 (by omega)
    obtain ⟨⟨vc, hvc, hvcw⟩, hkc⟩ := known_cout_plain_1
    exact ripple_final hN hA hB hCi eq_c_plain_0 eq_c_g_bit_1 eq_s_g_bit_0 eq_cout_plain_1 hvs
      (by omega) (fun k hk => (known_s_g_bit_0 k hk).2) hvc hvcw hkc))

/-! ## 1. The produced equation is the tampered one -/

theorem bad_gate_eq (N : Nat) (hN : 1 ≤ N) :
    bad_gate.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
        ∀ i, i < N → st.boolAt "s" i = (st.boolAt "a" i || (st.boolAt "b" i ^^ st.boolAt "c" i)) := by
  have hc : CombDesign (bad_gate.sem N) := by sv_structure; all_goals (intros; omega)
  have ha : Acyclic (bad_gate.sem N) := by
    sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y ci hA hB hCi
  sv_equations
  · exact eq_s_g_bit_0
  ripple_obligations

theorem bad_offset_eq (N : Nat) (hN : 1 ≤ N) :
    bad_offset.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
        ∀ i, i < N → st.boolAt "s" i =
          (st.boolAt "a" i ^^ st.boolAt "b" ((N : Int) + -1 * (i : Int) + -1).toNat ^^ st.boolAt "c" i) := by
  have hc : CombDesign (bad_offset.sem N) := by sv_structure; all_goals (intros; omega)
  have ha : Acyclic (bad_offset.sem N) := by
    sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y ci hA hB hCi
  sv_equations
  · exact eq_s_g_bit_0
  ripple_obligations

theorem bad_carry_eq (N : Nat) (hN : 1 ≤ N) :
    bad_carry.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
        st.boolAt "c" N = st.boolAt "cin" 0 ∧ st.boolAt "cout" 0 = st.boolAt "c" 0 := by
  have hc : CombDesign (bad_carry.sem N) := by sv_structure; all_goals (intros; omega)
  have ha : Acyclic (bad_carry.sem N) := by
    sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => N - i.toNat))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y ci hA hB hCi
  sv_equations
  · exact ⟨eq_c_plain_0, eq_cout_plain_1⟩
  ripple_obligations

/-! ## 2. The final proof FAILS on the tampered designs -/

-- Control: the same wrapper on the GENUINE adder. `fail_if_success (fail_if_success S)` holds iff
-- `S` succeeds, so this passes only because the genuine script proves the genuine statement; the
-- tests below are therefore real failures, not an artifact of the wrapper.
example (N : Nat) (hN : 1 ≤ N) : True := by
  fail_if_success
    fail_if_success
      have _ : ripple_add.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
          ∀ (x y : BitVec N) (ci : Bool),
            SvState.lookup st "a" = some (LVec.ofBitVec x) →
            SvState.lookup st "b" = some (LVec.ofBitVec y) →
            SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
            SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
            SvState.lookup st "cout" =
              some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) := by
        have hc : CombDesign (ripple_add.sem N) := by sv_structure; all_goals (intros; omega)
        have ha : Acyclic (ripple_add.sem N) := by
          sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1)
            (fun _ _ i => i.toNat + 1))
          all_goals (intros; omega)
        refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
        intro x y ci hA hB hCi
        sv_equations
        · ripple_close
        ripple_obligations
  trivial

example (N : Nat) (hN : 1 ≤ N) : True := by
  fail_if_success
    have _ : bad_gate.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
        ∀ (x y : BitVec N) (ci : Bool),
          SvState.lookup st "a" = some (LVec.ofBitVec x) →
          SvState.lookup st "b" = some (LVec.ofBitVec y) →
          SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
          SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
          SvState.lookup st "cout" =
            some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) := by
      have hc : CombDesign (bad_gate.sem N) := by sv_structure; all_goals (intros; omega)
      have ha : Acyclic (bad_gate.sem N) := by
        sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1)
          (fun _ _ i => i.toNat + 1))
        all_goals (intros; omega)
      refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
      intro x y ci hA hB hCi
      sv_equations
      · ripple_close
      ripple_obligations
  trivial

example (N : Nat) (hN : 1 ≤ N) : True := by
  fail_if_success
    have _ : bad_offset.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
        ∀ (x y : BitVec N) (ci : Bool),
          SvState.lookup st "a" = some (LVec.ofBitVec x) →
          SvState.lookup st "b" = some (LVec.ofBitVec y) →
          SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
          SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
          SvState.lookup st "cout" =
            some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) := by
      have hc : CombDesign (bad_offset.sem N) := by sv_structure; all_goals (intros; omega)
      have ha : Acyclic (bad_offset.sem N) := by
        sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1)
          (fun _ _ i => i.toNat + 1))
        all_goals (intros; omega)
      refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
      intro x y ci hA hB hCi
      sv_equations
      · ripple_close
      ripple_obligations
  trivial

example (N : Nat) (hN : 1 ≤ N) : True := by
  fail_if_success
    have _ : bad_carry.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
        ∀ (x y : BitVec N) (ci : Bool),
          SvState.lookup st "a" = some (LVec.ofBitVec x) →
          SvState.lookup st "b" = some (LVec.ofBitVec y) →
          SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) →
          SvState.lookup st "s" = some (LVec.ofBitVec (x + y + (BitVec.ofBool ci).setWidth N)) ∧
          SvState.lookup st "cout" =
            some (LVec.ofBitVec (BitVec.ofBool (2 ^ N ≤ x.toNat + y.toNat + ci.toNat))) := by
      have hc : CombDesign (bad_carry.sem N) := by sv_structure; all_goals (intros; omega)
      have ha : Acyclic (bad_carry.sem N) := by
        sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1)
          (fun _ _ i => N - i.toNat))
        all_goals (intros; omega)
      refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
      intro x y ci hA hB hCi
      sv_equations
      · ripple_close
      ripple_obligations
  trivial

end Examples.«system-verilog».ripple_add.neg
