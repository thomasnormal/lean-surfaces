import Examples.«system-verilog».comb_word.gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombProcTactic

/-!
# `sv_equations?` on the word-level designs (WP-B2)

What the player sees. A sum is stated in the faithful nested form of the SystemVerilog over the BIT FUNCTIONS of
its operands: `XF.addBits W f W g k` is bit `k` of `val f W + val g W`, `XF.subBits` the difference modulo `2^W`,
`XF.zext n f` the zero extension of an `n`-bit operand (what slang's `Resize` marker computes). `W` is the CONTEXT
width: the target's (`N + 1` for `add_wide`, `sub_wide`, `addw`'s `t`), not the operands'. A bare operand as wide as
the target prints as the bit function itself (`add_same`). The select `s = t[N-1:0]` and `cout = t[N]` of `addw` are
plain copies. The obligation `width` is the contract `n ≤ W` (a marker wider than its context would be a
truncation); it is closed by `omega`. Pinned verbatim.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».comb_word.gen

namespace Examples.«system-verilog».comb_word.comb_hint

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_y_plain_0 : ∀ (k : Nat),
  k < N + 1 →
    st.boolAt "y" k =
      XF.addBits (N + 1) (fun x => XF.zext ((↑N + -1).natAbs + 1) (fun k => st.boolAt "a" k) x) (N + 1)
        (fun x => XF.zext ((↑N + -1).natAbs + 1) (fun k => st.boolAt "b" k) x) k
  known_y_plain_0 : ∀ (k : Nat), k < N + 1 → (∃ v, st.lookup "y" = some v ∧ v.width = N + 1) ∧ KnownBit st "y" k
  stable aliases (copies of the above; same statements):
    eq_y_1 := eq_y_plain_0    known_y_1 := known_y_plain_0
  [width] ⊢ (↑N + -1).natAbs ≤ N
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (add_wide.sem N)) (ha : Acyclic (add_wide.sem N)) (st : SvState)
    (heqs : CombEqs (add_wide.sem N) st) (hsh : StateShape (add_wide.sem N) st) : True := by
  sv_equations?
  trivial

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_d_plain_0 : ∀ (k : Nat),
  k < N + 1 →
    st.boolAt "d" k =
      XF.subBits (N + 1) (fun x => XF.zext ((↑N + -1).natAbs + 1) (fun k => st.boolAt "a" k) x) (N + 1)
        (fun x => XF.zext ((↑N + -1).natAbs + 1) (fun k => st.boolAt "b" k) x) k
  known_d_plain_0 : ∀ (k : Nat), k < N + 1 → (∃ v, st.lookup "d" = some v ∧ v.width = N + 1) ∧ KnownBit st "d" k
  stable aliases (copies of the above; same statements):
    eq_d_1 := eq_d_plain_0    known_d_1 := known_d_plain_0
  [width] ⊢ (↑N + -1).natAbs ≤ N
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (sub_wide.sem N)) (ha : Acyclic (sub_wide.sem N)) (st : SvState)
    (heqs : CombEqs (sub_wide.sem N) st) (hsh : StateShape (sub_wide.sem N) st) : True := by
  sv_equations?
  trivial

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_y_plain_0 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 →
    st.boolAt "y" k =
      XF.addBits ((↑N + -1).natAbs + 1) (fun x => st.boolAt "a" x) ((↑N + -1).natAbs + 1) (fun x => st.boolAt "b" x) k
  known_y_plain_0 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 → (∃ v, st.lookup "y" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "y" k
  stable aliases (copies of the above; same statements):
    eq_y_1 := eq_y_plain_0    known_y_1 := known_y_plain_0
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (add_same.sem N)) (ha : Acyclic (add_same.sem N)) (st : SvState)
    (heqs : CombEqs (add_same.sem N) st) (hsh : StateShape (add_same.sem N) st) : True := by
  sv_equations?
  trivial

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_t_plain_0 : ∀ (k : Nat),
  k < N + 1 →
    st.boolAt "t" k =
      XF.addBits (N + 1)
        (fun x =>
          XF.addBits (N + 1) (fun x => XF.zext ((↑N + -1).natAbs + 1) (fun k => st.boolAt "a" k) x) (N + 1)
            (fun x => XF.zext ((↑N + -1).natAbs + 1) (fun k => st.boolAt "b" k) x) x)
        (N + 1) (fun x => XF.zext 1 (fun k => st.boolAt "cin" k) x) k
  eq_s_plain_1 : ∀ (k : Nat), k < (↑N + -1).natAbs + 1 → st.boolAt "s" k = st.boolAt "t" k
  eq_cout_plain_2 : st.boolAt "cout" 0 = st.boolAt "t" N
  known_t_plain_0 : ∀ (k : Nat), k < N + 1 → (∃ v, st.lookup "t" = some v ∧ v.width = N + 1) ∧ KnownBit st "t" k
  known_s_plain_1 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 → (∃ v, st.lookup "s" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "s" k
  known_cout_plain_2 : (∃ v, st.lookup "cout" = some v ∧ v.width = 1) ∧ KnownBit st "cout" 0
  stable aliases (copies of the above; same statements):
    eq_t_1 := eq_t_plain_0    known_t_1 := known_t_plain_0
    eq_s_1 := eq_s_plain_1    known_s_1 := known_s_plain_1
    eq_cout_1 := eq_cout_plain_2    known_cout_1 := known_cout_plain_2
  [width_1] ⊢ (↑N + -1).natAbs ≤ N
  [width_2] ⊢ (↑N + -1 + 1).toNat = (↑N + -1).natAbs + 1
  [cover] ⊢ ∀ (k : Nat), ↑k < ↑N + -1 + 1 → k < N + 1
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_3] ⊢ ∃ v, st.lookup "cin" = some v ∧ v.allKnown = true ∧ v.width = 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (addw.sem N)) (ha : Acyclic (addw.sem N)) (st : SvState)
    (heqs : CombEqs (addw.sem N) st) (hsh : StateShape (addw.sem N) st) : True := by
  sv_equations?
  trivial

-- `addp`: the sums in the two leaves of the tree (WP-B2 gate 2)
/--
info: sv_equations: the netlist view and the obligations (lowered design)
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_y_plain_0 : ∀ (k : Nat),
  k < N + 1 →
    st.boolAt "y" k =
      if st.boolAt "c" 0 = true then
        XF.addBits (N + 1) (fun x => XF.zext ((↑N + -1).natAbs + 1) (fun k => st.boolAt "a" k) x) (N + 1)
          (fun x => XF.zext ((↑N + -1).natAbs + 1) (fun k => st.boolAt "b" k) x) k
      else
        XF.subBits (N + 1) (fun x => XF.zext ((↑N + -1).natAbs + 1) (fun k => st.boolAt "a" k) x) (N + 1)
          (fun x => XF.zext ((↑N + -1).natAbs + 1) (fun k => st.boolAt "b" k) x) k
  known_y_plain_0 : ∀ (k : Nat), k < N + 1 → (∃ v, st.lookup "y" = some v ∧ v.width = N + 1) ∧ KnownBit st "y" k
  stable aliases (copies of the above; same statements):
    eq_y_1 := eq_y_plain_0    known_y_1 := known_y_plain_0
  [width] ⊢ (↑N + -1).natAbs ≤ N
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_3] ⊢ ∃ v, st.lookup "c" = some v ∧ v.allKnown = true ∧ v.width = 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) {d' : Design2} (hl : (addp.sem N).lowerComb = some d')
    (hc : CombDesign d') (ha : Acyclic d') (st : SvState) (heqs : CombEqs d' st)
    (hsh : StateShape d' st) : True := by
  sv_equations?
  trivial

-- `cmp_same`, `cmp_mixed`, `trunc_inc`: WP-B2 gate 2b
/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_eq_plain_0 : st.boolAt "eq" 0 = XF.eqv ((↑N + -1).natAbs + 1) (fun x => st.boolAt "a" x) fun x => st.boolAt "b" x
  eq_ne_plain_1 : st.boolAt "ne" 0 = !XF.eqv ((↑N + -1).natAbs + 1) (fun x => st.boolAt "a" x) fun x => st.boolAt "b" x
  eq_lt_plain_2 : st.boolAt "lt" 0 =
  decide
    (XF.val (fun x => st.boolAt "a" x) ((↑N + -1).natAbs + 1) <
      XF.val (fun x => st.boolAt "b" x) ((↑N + -1).natAbs + 1))
  eq_le_plain_3 : st.boolAt "le" 0 =
  decide
    (XF.val (fun x => st.boolAt "a" x) ((↑N + -1).natAbs + 1) ≤
      XF.val (fun x => st.boolAt "b" x) ((↑N + -1).natAbs + 1))
  eq_gt_plain_4 : st.boolAt "gt" 0 =
  decide
    (XF.val (fun x => st.boolAt "a" x) ((↑N + -1).natAbs + 1) >
      XF.val (fun x => st.boolAt "b" x) ((↑N + -1).natAbs + 1))
  eq_ge_plain_5 : st.boolAt "ge" 0 =
  decide
    (XF.val (fun x => st.boolAt "a" x) ((↑N + -1).natAbs + 1) ≥
      XF.val (fun x => st.boolAt "b" x) ((↑N + -1).natAbs + 1))
  known_eq_plain_0 : (∃ v, st.lookup "eq" = some v ∧ v.width = 1) ∧ KnownBit st "eq" 0
  known_ne_plain_1 : (∃ v, st.lookup "ne" = some v ∧ v.width = 1) ∧ KnownBit st "ne" 0
  known_lt_plain_2 : (∃ v, st.lookup "lt" = some v ∧ v.width = 1) ∧ KnownBit st "lt" 0
  known_le_plain_3 : (∃ v, st.lookup "le" = some v ∧ v.width = 1) ∧ KnownBit st "le" 0
  known_gt_plain_4 : (∃ v, st.lookup "gt" = some v ∧ v.width = 1) ∧ KnownBit st "gt" 0
  known_ge_plain_5 : (∃ v, st.lookup "ge" = some v ∧ v.width = 1) ∧ KnownBit st "ge" 0
  stable aliases (copies of the above; same statements):
    eq_eq_1 := eq_eq_plain_0    known_eq_1 := known_eq_plain_0
    eq_ne_1 := eq_ne_plain_1    known_ne_1 := known_ne_plain_1
    eq_lt_1 := eq_lt_plain_2    known_lt_1 := known_lt_plain_2
    eq_le_1 := eq_le_plain_3    known_le_1 := known_le_plain_3
    eq_gt_1 := eq_gt_plain_4    known_gt_1 := known_gt_plain_4
    eq_ge_1 := eq_ge_plain_5    known_ge_1 := known_ge_plain_5
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (cmp_same.sem N)) (ha : Acyclic (cmp_same.sem N)) (st : SvState)
    (heqs : CombEqs (cmp_same.sem N) st) (hsh : StateShape (cmp_same.sem N) st) : True := by
  sv_equations?
  trivial

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_y_lt_plain_0 : st.boolAt "y_lt" 0 =
  decide
    (XF.val (fun x => XF.zext ((↑N + -1).natAbs + 1) (fun k => st.boolAt "a" k) x)
        (max ((↑N + -1).natAbs + 1) ((↑N + 3).natAbs + 1)) <
      XF.val (fun x => st.boolAt "c" x) (max ((↑N + -1).natAbs + 1) ((↑N + 3).natAbs + 1)))
  eq_y_eq_plain_1 : st.boolAt "y_eq" 0 =
  XF.eqv (max ((↑N + -1).natAbs + 1) ((↑N + 3).natAbs + 1))
    (fun x => XF.zext ((↑N + -1).natAbs + 1) (fun k => st.boolAt "a" k) x) fun x => st.boolAt "c" x
  eq_y_k_plain_2 : st.boolAt "y_k" 0 =
  XF.eqv (max ((↑N + -1).natAbs + 1) 32) (fun x => XF.zext ((↑N + -1).natAbs + 1) (fun k => st.boolAt "a" k) x) fun x =>
    XF.constBit 3 (max ((↑N + -1).natAbs + 1) 32) x
  eq_y_ge1_plain_3 : st.boolAt "y_ge1" 0 =
  decide
    (XF.val (fun x => XF.zext ((↑N + -1).natAbs + 1) (fun k => st.boolAt "a" k) x) (max ((↑N + -1).natAbs + 1) 32) ≥
      XF.val (fun x => XF.constBit 1 (max ((↑N + -1).natAbs + 1) 32) x) (max ((↑N + -1).natAbs + 1) 32))
  eq_y_zext_plain_4 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 →
    st.boolAt "y_zext" k =
      XF.zext 1
        (fun x =>
          decide
            (XF.val (fun x => XF.zext ((↑N + -1).natAbs + 1) (fun k => st.boolAt "a" k) x)
                (max ((↑N + -1).natAbs + 1) ((↑N + 3).natAbs + 1)) <
              XF.val (fun x => st.boolAt "c" x) (max ((↑N + -1).natAbs + 1) ((↑N + 3).natAbs + 1))))
        k
  known_y_lt_plain_0 : (∃ v, st.lookup "y_lt" = some v ∧ v.width = 1) ∧ KnownBit st "y_lt" 0
  known_y_eq_plain_1 : (∃ v, st.lookup "y_eq" = some v ∧ v.width = 1) ∧ KnownBit st "y_eq" 0
  known_y_k_plain_2 : (∃ v, st.lookup "y_k" = some v ∧ v.width = 1) ∧ KnownBit st "y_k" 0
  known_y_ge1_plain_3 : (∃ v, st.lookup "y_ge1" = some v ∧ v.width = 1) ∧ KnownBit st "y_ge1" 0
  known_y_zext_plain_4 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 →
    (∃ v, st.lookup "y_zext" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "y_zext" k
  stable aliases (copies of the above; same statements):
    eq_y_lt_1 := eq_y_lt_plain_0    known_y_lt_1 := known_y_lt_plain_0
    eq_y_eq_1 := eq_y_eq_plain_1    known_y_eq_1 := known_y_eq_plain_1
    eq_y_k_1 := eq_y_k_plain_2    known_y_k_1 := known_y_k_plain_2
    eq_y_ge1_1 := eq_y_ge1_plain_3    known_y_ge1_1 := known_y_ge1_plain_3
    eq_y_zext_1 := eq_y_zext_plain_4    known_y_zext_1 := known_y_zext_plain_4
  [width_1] ⊢ (↑N + -1).natAbs ≤ max (↑N + -1).natAbs (↑N + 3).natAbs
  [width_2] ⊢ (↑N + 3).natAbs = max (↑N + -1).natAbs (↑N + 3).natAbs
  [width_3] ⊢ (↑N + -1).natAbs + 1 ≤ max ((↑N + -1).natAbs + 1) 32
  [width_4] ⊢ (↑N + -1).natAbs ≤ max (↑N + -1).natAbs (↑N + 3).natAbs
  [width_5] ⊢ (↑N + 3).natAbs = max (↑N + -1).natAbs (↑N + 3).natAbs
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "c" = some v ∧ v.allKnown = true ∧ v.width = (↑N + 3).natAbs + 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (cmp_mixed.sem N)) (ha : Acyclic (cmp_mixed.sem N)) (st : SvState)
    (heqs : CombEqs (cmp_mixed.sem N) st) (hsh : StateShape (cmp_mixed.sem N) st) : True := by
  sv_equations?
  trivial

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_t_plain_0 : ∀ (k : Nat),
  k < (↑N + -2).natAbs + 1 →
    st.boolAt "t" k =
      if (↑N + -1).natAbs + 1 < (↑N + -2).natAbs + 1 then
        XF.addBits ((↑N + -2).natAbs + 1) (fun x => st.boolAt "a" x) ((↑N + -2).natAbs + 1) (fun x => st.boolAt "b" x) k
      else
        XF.zext ((↑N + -1).natAbs + 1)
          (fun x =>
            XF.addBits ((↑N + -1).natAbs + 1) (fun x => st.boolAt "a" x) ((↑N + -1).natAbs + 1)
              (fun x => st.boolAt "b" x) x)
          k
  eq_y1_plain_1 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 →
    st.boolAt "y1" k =
      if max ((↑N + -1).natAbs + 1) 32 < (↑N + -1).natAbs + 1 then
        XF.addBits ((↑N + -1).natAbs + 1) (fun x => XF.zext ((↑N + -1).natAbs + 1) (fun x => st.boolAt "a" x) x)
          ((↑N + -1).natAbs + 1) (fun x => XF.constBit 1 ((↑N + -1).natAbs + 1) x) k
      else
        XF.zext (max ((↑N + -1).natAbs + 1) 32)
          (fun x =>
            XF.addBits (max ((↑N + -1).natAbs + 1) 32)
              (fun x => XF.zext ((↑N + -1).natAbs + 1) (fun x => st.boolAt "a" x) x) (max ((↑N + -1).natAbs + 1) 32)
              (fun x => XF.constBit 1 (max ((↑N + -1).natAbs + 1) 32) x) x)
          k
  eq_y2_plain_2 : ∀ (k : Nat),
  k < N + 1 →
    st.boolAt "y2" k =
      if max ((↑N + -1).natAbs + 1) 32 < N + 1 then
        XF.subBits (N + 1) (fun x => XF.zext ((↑N + -1).natAbs + 1) (fun x => st.boolAt "a" x) x) (N + 1)
          (fun x => XF.constBit 1 (N + 1) x) k
      else
        XF.zext (max ((↑N + -1).natAbs + 1) 32)
          (fun x =>
            XF.subBits (max ((↑N + -1).natAbs + 1) 32)
              (fun x => XF.zext ((↑N + -1).natAbs + 1) (fun x => st.boolAt "a" x) x) (max ((↑N + -1).natAbs + 1) 32)
              (fun x => XF.constBit 1 (max ((↑N + -1).natAbs + 1) 32) x) x)
          k
  known_t_plain_0 : ∀ (k : Nat),
  k < (↑N + -2).natAbs + 1 → (∃ v, st.lookup "t" = some v ∧ v.width = (↑N + -2).natAbs + 1) ∧ KnownBit st "t" k
  known_y1_plain_1 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 → (∃ v, st.lookup "y1" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "y1" k
  known_y2_plain_2 : ∀ (k : Nat), k < N + 1 → (∃ v, st.lookup "y2" = some v ∧ v.width = N + 1) ∧ KnownBit st "y2" k
  stable aliases (copies of the above; same statements):
    eq_t_1 := eq_t_plain_0    known_t_1 := known_t_plain_0
    eq_y1_1 := eq_y1_plain_1    known_y1_1 := known_y1_plain_1
    eq_y2_1 := eq_y2_plain_2    known_y2_1 := known_y2_plain_2
  [width_1] ⊢ (↑N + -1).natAbs < (↑N + -2).natAbs → (↑N + -1).natAbs = (↑N + -2).natAbs
  [width_2] ⊢ if max ((↑N + -1).natAbs + 1) 32 < N + 1 then (↑N + -1).natAbs ≤ N
else (↑N + -1).natAbs + 1 ≤ max ((↑N + -1).natAbs + 1) 32
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 2 ≤ N) (hc : CombDesign (trunc_inc.sem N)) (ha : Acyclic (trunc_inc.sem N)) (st : SvState)
    (heqs : CombEqs (trunc_inc.sem N) st) (hsh : StateShape (trunc_inc.sem N) st) : True := by
  sv_equations?
  trivial

/-! ### Run-time shifts (WP-B2 gate 3)

`a << s` and `a >> s` print `XF.shlBits` / `XF.shrBits` over the bit functions of the operand and of the AMOUNT:
`XF.shlBits f wr g k` is bit `k` of `f` shifted left by the value of the `wr`-bit amount `g`. The left operand is
context-determined, so a shift into a wider target prints it zero-extended (`XF.zext W …`, `shl_wide`); the amount is
self-determined and never widens the result (`Int.natAbs 2 + 1` is the 3 bits of `s : [2:0]`; an unsized constant amount is
32 bits wide, `shl_const`). `1 << s` (`onehot`): the unsized constant `1` is a SIGNED 32-bit integer, so slang lowers the
shift at `max N 32` bits and the left operand is SIGN-extended (`XF.sext 32 …`); the marker around the result is the
single `if` of the gate-2b truncation. No `width_k` goal appears for a shift: both operands are read at their own widths. -/

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_y_plain_0 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 →
    st.boolAt "y" k =
      XF.shlBits (XF.zext ((↑N + -1).natAbs + 1) fun x => st.boolAt "a" x) (Int.natAbs 2 + 1) (fun x => st.boolAt "s" x)
        k
  known_y_plain_0 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 → (∃ v, st.lookup "y" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "y" k
  stable aliases (copies of the above; same statements):
    eq_y_1 := eq_y_plain_0    known_y_1 := known_y_plain_0
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "s" = some v ∧ v.allKnown = true ∧ v.width = 3
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (shl_n.sem N)) (ha : Acyclic (shl_n.sem N)) (st : SvState)
    (heqs : CombEqs (shl_n.sem N) st) (hsh : StateShape (shl_n.sem N) st) : True := by
  sv_equations?
  trivial

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_y_plain_0 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 →
    st.boolAt "y" k =
      XF.shrBits ((↑N + -1).natAbs + 1) (fun x => st.boolAt "a" x) (Int.natAbs 2 + 1) (fun x => st.boolAt "s" x) k
  known_y_plain_0 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 → (∃ v, st.lookup "y" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "y" k
  stable aliases (copies of the above; same statements):
    eq_y_1 := eq_y_plain_0    known_y_1 := known_y_plain_0
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "s" = some v ∧ v.allKnown = true ∧ v.width = 3
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (shr_n.sem N)) (ha : Acyclic (shr_n.sem N)) (st : SvState)
    (heqs : CombEqs (shr_n.sem N) st) (hsh : StateShape (shr_n.sem N) st) : True := by
  sv_equations?
  trivial

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_y_plain_0 : ∀ (k : Nat),
  k < N + 1 →
    st.boolAt "y" k =
      XF.shlBits (XF.zext ((↑N + -1).natAbs + 1) fun x => st.boolAt "a" x) (Int.natAbs 2 + 1) (fun x => st.boolAt "s" x)
        k
  known_y_plain_0 : ∀ (k : Nat), k < N + 1 → (∃ v, st.lookup "y" = some v ∧ v.width = N + 1) ∧ KnownBit st "y" k
  stable aliases (copies of the above; same statements):
    eq_y_1 := eq_y_plain_0    known_y_1 := known_y_plain_0
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "s" = some v ∧ v.allKnown = true ∧ v.width = 3
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (shl_wide.sem N)) (ha : Acyclic (shl_wide.sem N)) (st : SvState)
    (heqs : CombEqs (shl_wide.sem N) st) (hsh : StateShape (shl_wide.sem N) st) : True := by
  sv_equations?
  trivial

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_y_plain_0 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 →
    st.boolAt "y" k =
      if 32 < (↑N + -1).natAbs + 1 then
        XF.shlBits (XF.sext 32 fun x => XF.constBit 1 32 x) (Int.natAbs 2 + 1) (fun x => st.boolAt "s" x) k
      else
        XF.zext 32
          (fun x => XF.shlBits (XF.sext 32 fun x => XF.constBit 1 32 x) (Int.natAbs 2 + 1) (fun x => st.boolAt "s" x) x)
          k
  known_y_plain_0 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 → (∃ v, st.lookup "y" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "y" k
  stable aliases (copies of the above; same statements):
    eq_y_1 := eq_y_plain_0    known_y_1 := known_y_plain_0
  [inputsKnown] ⊢ ∃ v, st.lookup "s" = some v ∧ v.allKnown = true ∧ v.width = 3
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (onehot.sem N)) (ha : Acyclic (onehot.sem N)) (st : SvState)
    (heqs : CombEqs (onehot.sem N) st) (hsh : StateShape (onehot.sem N) st) : True := by
  sv_equations?
  trivial

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_y_plain_0 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 →
    st.boolAt "y" k =
      XF.shlBits (XF.zext ((↑N + -1).natAbs + 1) fun x => st.boolAt "a" x) 32 (fun x => XF.constBit 1 32 x) k
  eq_z_plain_1 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 →
    st.boolAt "z" k = XF.shrBits ((↑N + -1).natAbs + 1) (fun x => st.boolAt "a" x) 32 (fun x => XF.constBit 2 32 x) k
  known_y_plain_0 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 → (∃ v, st.lookup "y" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "y" k
  known_z_plain_1 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 → (∃ v, st.lookup "z" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "z" k
  stable aliases (copies of the above; same statements):
    eq_y_1 := eq_y_plain_0    known_y_1 := known_y_plain_0
    eq_z_1 := eq_z_plain_1    known_z_1 := known_z_plain_1
  [inputsKnown] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (shl_const.sem N)) (ha : Acyclic (shl_const.sem N)) (st : SvState)
    (heqs : CombEqs (shl_const.sem N) st) (hsh : StateShape (shl_const.sem N) st) : True := by
  sv_equations?
  trivial

/-! ### Concatenations as operands (WP-B2 gate 3b)

A concatenation `{hi, lo}` prints as the bit function `if j < w2 then lo j else hi (j - w2)` (`w2` the width of the low
part; a literal part is a plain bit, or `LVec.boolAt` of the literal: a one-bit `1'b0` is `false`). Under a `Resize` marker the
concatenation is zero-extended like any operand (`XF.zext (W + 1) …` for `t`'s `{b, 1'b0}`); a bare concatenation as wide as
its context (`s`'s `{1'b0, a}`) is the bit function itself. The obligations are the widths of the parts (`width_1`,
`width_2`, `width_4`, `width_5`: every concatenation as wide as its context; a literal part other than `1'b0` shows as the width of the literal, which
`simp [LVec.width]` evaluates) and `width_3` (the marker around `{b, 1'b0}`
does not truncate). -/

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_s_plain_0 : ∀ (k : Nat),
  k < N + 1 →
    st.boolAt "s" k =
      XF.addBits (N + 1)
        (fun x =>
          XF.addBits (N + 1) (fun x => if x < (↑N + -1).natAbs + 1 then st.boolAt "a" x else false) (N + 1)
            (fun x => if x < (↑N + -1).natAbs + 1 then st.boolAt "b" x else false) x)
        (N + 1) (fun x => XF.zext 1 (fun k => st.boolAt "cin" k) x) k
  eq_t_plain_1 : ∀ (k : Nat),
  k < (↑N + 1).natAbs + 1 →
    st.boolAt "t" k =
      XF.addBits ((↑N + 1).natAbs + 1)
        (fun x =>
          if x < (↑N + -1).natAbs + 1 then st.boolAt "a" x
          else { bits := #[Logic.l0, Logic.l0] }.boolAt (x - ((↑N + -1).natAbs + 1)))
        ((↑N + 1).natAbs + 1)
        (fun x => XF.zext ((↑N + -1).natAbs + 1 + 1) (fun x => if x = 0 then false else st.boolAt "b" (x - 1)) x) k
  eq_w_plain_2 : ∀ (k : Nat),
  k < N + 1 →
    st.boolAt "w" k =
      if st.boolAt "cin" 0 = true then if k = 0 then false else st.boolAt "a" (k - 1)
      else
        if k < (↑N + -1).natAbs + 1 then st.boolAt "a" k
        else { bits := #[Logic.l1] }.boolAt (k - ((↑N + -1).natAbs + 1))
  eq_e_plain_3 : st.boolAt "e" 0 =
  XF.eqv ((↑N + -1).natAbs + 1 + ((↑N + -1).natAbs + 1))
    (fun x => if x < (↑N + -1).natAbs + 1 then st.boolAt "b" x else st.boolAt "a" (x - ((↑N + -1).natAbs + 1))) fun x =>
    if x < (↑N + -1).natAbs + 1 then st.boolAt "a" x else st.boolAt "b" (x - ((↑N + -1).natAbs + 1))
  known_s_plain_0 : ∀ (k : Nat), k < N + 1 → (∃ v, st.lookup "s" = some v ∧ v.width = N + 1) ∧ KnownBit st "s" k
  known_t_plain_1 : ∀ (k : Nat), k < (↑N + 1).natAbs + 1 → (∃ v, st.lookup "t" = some v ∧ v.width = (↑N + 1).natAbs + 1) ∧ KnownBit st "t" k
  known_w_plain_2 : ∀ (k : Nat), k < N + 1 → (∃ v, st.lookup "w" = some v ∧ v.width = N + 1) ∧ KnownBit st "w" k
  known_e_plain_3 : (∃ v, st.lookup "e" = some v ∧ v.width = 1) ∧ KnownBit st "e" 0
  stable aliases (copies of the above; same statements):
    eq_s_1 := eq_s_plain_0    known_s_1 := known_s_plain_0
    eq_t_1 := eq_t_plain_1    known_t_1 := known_t_plain_1
    eq_w_1 := eq_w_plain_2    known_w_1 := known_w_plain_2
    eq_e_1 := eq_e_plain_3    known_e_1 := known_e_plain_3
  [width_1] ⊢ 1 + ((↑N + -1).natAbs + 1) = N + 1
  [width_2] ⊢ { bits := #[Logic.l0, Logic.l0] }.width + ((↑N + -1).natAbs + 1) = (↑N + 1).natAbs + 1
  [width_3] ⊢ (↑N + -1).natAbs + 1 ≤ (↑N + 1).natAbs
  [width_4] ⊢ (↑N + -1).natAbs + 1 = N
  [width_5] ⊢ { bits := #[Logic.l1] }.width + ((↑N + -1).natAbs + 1) = N + 1
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_3] ⊢ ∃ v, st.lookup "cin" = some v ∧ v.allKnown = true ∧ v.width = 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (cat_add.sem N)) (ha : Acyclic (cat_add.sem N)) (st : SvState)
    (heqs : CombEqs (cat_add.sem N) st) (hsh : StateShape (cat_add.sem N) st) : True := by
  sv_equations?
  trivial

/-! ## Rows and part selects (WP-B2 gate 4a)

A legacy select of a two-dimensional declaration is a whole ROW: the equation of `r[i + 1] = ~r[i]` is over the row-major
offset `rmN W (↑i + 1) 0 + k` (the stride `W` is the printed row width: `↑N`, `2 * ↑N`, `3`), and the obligations are the
row indices (`inRange`), the widths and the two coverage goals (the row a loop iteration reads is written by the plain
site or by the previous iteration). A constant-bound part select is a window of the declared signal at `Int.toNat lo + k`
(`ps_rot`, whose netlist is flat and whose structural obligations are decided: the line `decided …`), and a part select
whose bounds are affine in the genvar is the window `(4 * ↑i).toNat + k`. Pinned verbatim. -/

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_r_plain_0 : ∀ (k : Nat), k < N → st.boolAt "r" k = st.boolAt "x" k
  eq_y_plain_1 : ∀ (k : Nat), k < (↑N + -1).natAbs + 1 → st.boolAt "y" k = st.boolAt "r" (rmN (↑N) (↑N) 0 + k)
  eq_r_g_0 : ∀ (i : Nat), i < N → ∀ (k : Nat), k < N → st.boolAt "r" (rmN (↑N) (↑i + 1) 0 + k) = !st.boolAt "r" (rmN (↑N) (↑i) 0 + k)
  known_r_plain_0 : ∀ (k : Nat), k < N → (∃ v, st.lookup "r" = some v ∧ v.width = (N + 1) * ((↑N + -1).natAbs + 1)) ∧ KnownBit st "r" k
  known_y_plain_1 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 → (∃ v, st.lookup "y" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "y" k
  known_r_g_0 : ∀ (i : Nat),
  i < N →
    ∀ (k : Nat),
      k < N →
        (∃ v, st.lookup "r" = some v ∧ v.width = (N + 1) * ((↑N + -1).natAbs + 1)) ∧
          KnownBit st "r" (rmN (↑N) (↑i + 1) 0 + k)
  stable aliases (copies of the above; same statements):
    eq_r_1 := eq_r_plain_0    known_r_1 := known_r_plain_0
    eq_y_1 := eq_y_plain_1    known_y_1 := known_y_plain_1
    eq_r_2 := eq_r_g_0    known_r_2 := known_r_g_0
  [inRange] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → 0 ≤ i + 1 ∧ i + 1 ≤ ↑N
  [width_1] ⊢ (↑N + -1).natAbs + 1 = N
  [width_2] ⊢ N = (↑N + -1).natAbs + 1
  [cover_1] ⊢ ∀ (k : Nat),
  k < N →
    rmN (↑N) 0 0 ≤ rmN (↑N) (↑N) 0 + k ∧ rmN (↑N) (↑N) 0 + k < rmN (↑N) 0 0 + N ∨
      ∃ i, i < N ∧ rmN (↑N) (↑i + 1) 0 ≤ rmN (↑N) (↑N) 0 + k ∧ rmN (↑N) (↑N) 0 + k < rmN (↑N) (↑i + 1) 0 + N
  [cover_2] ⊢ ∀ (i : Int),
  0 ≤ i →
    i < ↑N →
      ∀ (k : Nat),
        k < N →
          rmN (↑N) 0 0 ≤ rmN (↑N) i 0 + k ∧ rmN (↑N) i 0 + k < rmN (↑N) 0 0 + N ∨
            ∃ i_1, i_1 < N ∧ rmN (↑N) (↑i_1 + 1) 0 ≤ rmN (↑N) i 0 + k ∧ rmN (↑N) i 0 + k < rmN (↑N) (↑i_1 + 1) 0 + N
  [inputsKnown] ⊢ ∃ v, st.lookup "x" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (row_chain.sem N)) (ha : Acyclic (row_chain.sem N)) (st : SvState)
    (heqs : CombEqs (row_chain.sem N) st) (hsh : StateShape (row_chain.sem N) st) : True := by
  sv_equations?
  trivial

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_r_plain_0 : ∀ (k : Nat), k < (2 * ↑N).toNat → st.boolAt "r" k = st.boolAt "x" k
  eq_y_plain_1 : ∀ (k : Nat), k < (2 * ↑N + -1).natAbs + 1 → st.boolAt "y" k = st.boolAt "r" (rmN (2 * ↑N) (↑N) 0 + k)
  eq_r_g_0 : ∀ (i : Nat),
  i < N →
    ∀ (k : Nat),
      k < (2 * ↑N).toNat → st.boolAt "r" (rmN (2 * ↑N) (↑i + 1) 0 + k) = !st.boolAt "r" (rmN (2 * ↑N) (↑i) 0 + k)
  known_r_plain_0 : ∀ (k : Nat),
  k < (2 * ↑N).toNat →
    (∃ v, st.lookup "r" = some v ∧ v.width = ((↑N + 1 + -1).natAbs + 1) * ((2 * ↑N + -1).natAbs + 1)) ∧
      KnownBit st "r" k
  known_y_plain_1 : ∀ (k : Nat),
  k < (2 * ↑N + -1).natAbs + 1 → (∃ v, st.lookup "y" = some v ∧ v.width = (2 * ↑N + -1).natAbs + 1) ∧ KnownBit st "y" k
  known_r_g_0 : ∀ (i : Nat),
  i < N →
    ∀ (k : Nat),
      k < (2 * ↑N).toNat →
        (∃ v, st.lookup "r" = some v ∧ v.width = ((↑N + 1 + -1).natAbs + 1) * ((2 * ↑N + -1).natAbs + 1)) ∧
          KnownBit st "r" (rmN (2 * ↑N) (↑i + 1) 0 + k)
  stable aliases (copies of the above; same statements):
    eq_r_1 := eq_r_plain_0    known_r_1 := known_r_plain_0
    eq_y_1 := eq_y_plain_1    known_y_1 := known_y_plain_1
    eq_r_2 := eq_r_g_0    known_r_2 := known_r_g_0
  [inRange_1] ⊢ 0 ≤ ↑N + 1 + -1
  [inRange_2] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → 0 ≤ i + 1 ∧ i + 1 ≤ ↑N + 1 + -1
  [width_1] ⊢ (2 * ↑N + -1).natAbs + 1 = (2 * ↑N).toNat
  [width_2] ⊢ (2 * ↑N).toNat = (2 * ↑N + -1).natAbs + 1
  [cover_1] ⊢ ∀ (k : Nat),
  ↑k < 2 * ↑N →
    rmN (2 * ↑N) 0 0 ≤ rmN (2 * ↑N) (↑N) 0 + k ∧ rmN (2 * ↑N) (↑N) 0 + k < rmN (2 * ↑N) 0 0 + (2 * ↑N).toNat ∨
      ∃ i,
        i < N ∧
          rmN (2 * ↑N) (↑i + 1) 0 ≤ rmN (2 * ↑N) (↑N) 0 + k ∧
            rmN (2 * ↑N) (↑N) 0 + k < rmN (2 * ↑N) (↑i + 1) 0 + (2 * ↑N).toNat
  [cover_2] ⊢ ∀ (i : Int),
  0 ≤ i →
    i < ↑N →
      ∀ (k : Nat),
        ↑k < 2 * ↑N →
          rmN (2 * ↑N) 0 0 ≤ rmN (2 * ↑N) i 0 + k ∧ rmN (2 * ↑N) i 0 + k < rmN (2 * ↑N) 0 0 + (2 * ↑N).toNat ∨
            ∃ i_1,
              i_1 < N ∧
                rmN (2 * ↑N) (↑i_1 + 1) 0 ≤ rmN (2 * ↑N) i 0 + k ∧
                  rmN (2 * ↑N) i 0 + k < rmN (2 * ↑N) (↑i_1 + 1) 0 + (2 * ↑N).toNat
  [inputsKnown] ⊢ ∃ v, st.lookup "x" = some v ∧ v.allKnown = true ∧ v.width = (2 * ↑N + -1).natAbs + 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (row_chain_lp.sem N)) (ha : Acyclic (row_chain_lp.sem N)) (st : SvState)
    (heqs : CombEqs (row_chain_lp.sem N) st) (hsh : StateShape (row_chain_lp.sem N) st) : True := by
  sv_equations?
  trivial

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_r_plain_0 : ∀ (k : Nat), k < Int.toNat 3 → st.boolAt "r" k = st.boolAt "x" k
  eq_y_plain_1 : ∀ (k : Nat), k < Int.natAbs 2 + 1 → st.boolAt "y" k = st.boolAt "r" (rmN 3 3 0 + k)
  eq_r_g_0 : ∀ (i : Nat),
  ↑i < 3 → ∀ (k : Nat), k < Int.toNat 3 → st.boolAt "r" (rmN 3 (↑i + 1) 0 + k) = !st.boolAt "r" (rmN 3 (↑i) 0 + k)
  known_r_plain_0 : ∀ (k : Nat),
  k < Int.toNat 3 →
    (∃ v, st.lookup "r" = some v ∧ v.width = (Int.natAbs 3 + 1) * (Int.natAbs 2 + 1)) ∧ KnownBit st "r" k
  known_y_plain_1 : ∀ (k : Nat), k < Int.natAbs 2 + 1 → (∃ v, st.lookup "y" = some v ∧ v.width = Int.natAbs 2 + 1) ∧ KnownBit st "y" k
  known_r_g_0 : ∀ (i : Nat),
  ↑i < 3 →
    ∀ (k : Nat),
      k < Int.toNat 3 →
        (∃ v, st.lookup "r" = some v ∧ v.width = (Int.natAbs 3 + 1) * (Int.natAbs 2 + 1)) ∧
          KnownBit st "r" (rmN 3 (↑i + 1) 0 + k)
  stable aliases (copies of the above; same statements):
    eq_r_1 := eq_r_plain_0    known_r_1 := known_r_plain_0
    eq_y_1 := eq_y_plain_1    known_y_1 := known_y_plain_1
    eq_r_2 := eq_r_g_0    known_r_2 := known_r_g_0
  [inRange] ⊢ ∀ (i : Int), 0 ≤ i → i < 3 → 0 ≤ i + 1 ∧ i + 1 ≤ 3
  [cover_1] ⊢ ∀ (k : Nat),
  k < 3 →
    rmN 3 0 0 ≤ rmN 3 3 0 + k ∧ rmN 3 3 0 + k < rmN 3 0 0 + 3 ∨
      ∃ i, ↑i < 3 ∧ rmN 3 (↑i + 1) 0 ≤ rmN 3 3 0 + k ∧ rmN 3 3 0 + k < rmN 3 (↑i + 1) 0 + 3
  [cover_2] ⊢ ∀ (i : Int),
  0 ≤ i →
    i < 3 →
      ∀ (k : Nat),
        k < 3 →
          rmN 3 0 0 ≤ rmN 3 i 0 + k ∧ rmN 3 i 0 + k < rmN 3 0 0 + 3 ∨
            ∃ i_1, ↑i_1 < 3 ∧ rmN 3 (↑i_1 + 1) 0 ≤ rmN 3 i 0 + k ∧ rmN 3 i 0 + k < rmN 3 (↑i_1 + 1) 0 + 3
  [inputsKnown] ⊢ ∃ v, st.lookup "x" = some v ∧ v.allKnown = true ∧ v.width = 3
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (hc : CombDesign (row_chain_lit.sem)) (ha : Acyclic (row_chain_lit.sem)) (st : SvState)
    (heqs : CombEqs (row_chain_lit.sem) st) (hsh : StateShape (row_chain_lit.sem) st) : True := by
  sv_equations?
  trivial

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_r_plain_0 : ∀ (k : Nat),
  k < Int.natAbs 15 + 1 →
    st.boolAt "r" k =
      if k < (15 - 9 + 1).toNat then st.boolAt "x" (Int.toNat 9 + k) else st.boolAt "x" (k - (15 - 9 + 1).toNat)
  eq_sw_plain_1 : ∀ (k : Nat), k < Int.toNat 8 → st.boolAt "sw" k = st.boolAt "x" (Int.toNat 8 + k)
  eq_sw_plain_2 : ∀ (k : Nat), k < (15 - 8 + 1).toNat → st.boolAt "sw" (Int.toNat 8 + k) = st.boolAt "x" k
  eq_e_plain_3 : ∀ (k : Nat), k < Int.natAbs 4 + 1 → st.boolAt "e" k = st.boolAt "x" (Int.toNat 10 + k)
  known_r_plain_0 : ∀ (k : Nat), k < Int.natAbs 15 + 1 → (∃ v, st.lookup "r" = some v ∧ v.width = Int.natAbs 15 + 1) ∧ KnownBit st "r" k
  known_sw_plain_1 : ∀ (k : Nat), k < Int.toNat 8 → (∃ v, st.lookup "sw" = some v ∧ v.width = Int.natAbs 15 + 1) ∧ KnownBit st "sw" k
  known_sw_plain_2 : ∀ (k : Nat),
  k < (15 - 8 + 1).toNat →
    (∃ v, st.lookup "sw" = some v ∧ v.width = Int.natAbs 15 + 1) ∧ KnownBit st "sw" (Int.toNat 8 + k)
  known_e_plain_3 : ∀ (k : Nat), k < Int.natAbs 4 + 1 → (∃ v, st.lookup "e" = some v ∧ v.width = Int.natAbs 4 + 1) ∧ KnownBit st "e" k
  stable aliases (copies of the above; same statements):
    eq_r_1 := eq_r_plain_0    known_r_1 := known_r_plain_0
    eq_sw_1 := eq_sw_plain_1    known_sw_1 := known_sw_plain_1
    eq_sw_2 := eq_sw_plain_2    known_sw_2 := known_sw_plain_2
    eq_e_1 := eq_e_plain_3    known_e_1 := known_e_plain_3
  decided (flat netlist: every site plain, no parameter): auto, inRange, width, bitRead, cover
  [inputsKnown] ⊢ ∃ v, st.lookup "x" = some v ∧ v.allKnown = true ∧ v.width = 16
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (hc : CombDesign (ps_rot.sem)) (ha : Acyclic (ps_rot.sem)) (st : SvState)
    (heqs : CombEqs (ps_rot.sem) st) (hsh : StateShape (ps_rot.sem) st) : True := by
  sv_equations?
  trivial

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_y_g_0 : ∀ (i : Nat),
  i < N →
    ∀ (k : Nat),
      k < (4 * ↑i + 3 - 4 * ↑i + 1).toNat → st.boolAt "y" ((4 * ↑i).toNat + k) = !st.boolAt "x" ((4 * ↑i).toNat + k)
  known_y_g_0 : ∀ (i : Nat),
  i < N →
    ∀ (k : Nat),
      k < (4 * ↑i + 3 - 4 * ↑i + 1).toNat →
        (∃ v, st.lookup "y" = some v ∧ v.width = (4 * ↑N + -1).natAbs + 1) ∧ KnownBit st "y" ((4 * ↑i).toNat + k)
  stable aliases (copies of the above; same statements):
    eq_y_1 := eq_y_g_0    known_y_1 := known_y_g_0
  [inRange] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → 0 ≤ 4 * i ∧ 4 * i ≤ 4 * i + 3 ∧ 4 * i + 3 ≤ 4 * ↑N + -1
  [cover] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → ∀ (k : Nat), ↑k < 4 * i + 3 - 4 * i + 1 → (4 * i).toNat + k < (4 * ↑N + -1).natAbs + 1
  [inputsKnown] ⊢ ∃ v, st.lookup "x" = some v ∧ v.allKnown = true ∧ v.width = (4 * ↑N + -1).natAbs + 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (ps_gen.sem N)) (ha : Acyclic (ps_gen.sem N)) (st : SvState)
    (heqs : CombEqs (ps_gen.sem N) st) (hsh : StateShape (ps_gen.sem N) st) : True := by
  sv_equations?
  trivial

/-! ## A genvar as the amount of a shift (WP-B2 gate 4b)

`aw << i` over a genvar prints the amount as the 32-bit literal of the genvar's value, `XF.constBit (↑i) 32`, the form an
unsized constant has (`shl_const`) with the variable `↑i` in place of the number. Pinned verbatim. -/

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_pp_g_0 : ∀ (i : Nat),
  i < N →
    ∀ (k : Nat),
      k < (2 * ↑N).toNat →
        st.boolAt "pp" (rmN (2 * ↑N) (↑i) 0 + k) =
          XF.shlBits (XF.zext ((2 * ↑N + -1).natAbs + 1) fun x => st.boolAt "aw" x) 32 (fun x => XF.constBit (↑i) 32 x)
            k
  known_pp_g_0 : ∀ (i : Nat),
  i < N →
    ∀ (k : Nat),
      k < (2 * ↑N).toNat →
        (∃ v, st.lookup "pp" = some v ∧ v.width = ((↑N + -1).natAbs + 1) * ((2 * ↑N + -1).natAbs + 1)) ∧
          KnownBit st "pp" (rmN (2 * ↑N) (↑i) 0 + k)
  stable aliases (copies of the above; same statements):
    eq_pp_1 := eq_pp_g_0    known_pp_1 := known_pp_g_0
  [inRange] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → 0 ≤ i ∧ i ≤ ↑N + -1
  [inputsKnown] ⊢ ∃ v, st.lookup "aw" = some v ∧ v.allKnown = true ∧ v.width = (2 * ↑N + -1).natAbs + 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (shl_gen.sem N)) (ha : Acyclic (shl_gen.sem N)) (st : SvState)
    (heqs : CombEqs (shl_gen.sem N) st) (hsh : StateShape (shl_gen.sem N) st) : True := by
  sv_equations?
  trivial

/-! ## Replication (WP-B2 gate 4c)

A replication is a PART of the concatenation (or the whole right-hand side): `{ {K{1'b0}}, x }` prints the literal part as the
guard `if k < N then st.boolAt "x" k else false`; the AND mask `a & {N{b[i]}}` reads bit `i` of `b` at every position
(`k % 1`, the width of the replicated bit select); a replicated part select with a literal count is `k % 2`. Pinned verbatim.
The count's non-negativity is an obligation only when the tactic cannot decide it (a parameter count: `0 ≤ ↑K` closes by
`Int.natCast_nonneg`, so no `[inRange]` line is left). A FLAT netlist with a replication (`repl_bits`) does not take the plain closure of
the in-range obligation (the premise "no site replicates" fails), so `inRange` is not in its `decided` line: the normalization route
closes it with nothing left. -/



/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_y_plain_0 : ∀ (k : Nat),
  k < (↑N + ↑K + -1).natAbs + 1 → st.boolAt "y" k = if k < (↑N + -1).natAbs + 1 then st.boolAt "x" k else false
  known_y_plain_0 : ∀ (k : Nat),
  k < (↑N + ↑K + -1).natAbs + 1 →
    (∃ v, st.lookup "y" = some v ∧ v.width = (↑N + ↑K + -1).natAbs + 1) ∧ KnownBit st "y" k
  stable aliases (copies of the above; same statements):
    eq_y_1 := eq_y_plain_0    known_y_1 := known_y_plain_0
  [width] ⊢ K + ((↑N + -1).natAbs + 1) = (↑N + ↑K + -1).natAbs + 1
  [inputsKnown] ⊢ ∃ v, st.lookup "x" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N K : Nat) (hN : 1 ≤ N) (hc : CombDesign (repl_pad.sem N K)) (ha : Acyclic (repl_pad.sem N K)) (st : SvState)
    (heqs : CombEqs (repl_pad.sem N K) st) (hsh : StateShape (repl_pad.sem N K) st) : True := by
  sv_equations?
  trivial



/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_pp_g_0 : ∀ (i : Nat),
  i < N → ∀ (k : Nat), k < N → st.boolAt "pp" (rmN (↑N) (↑i) 0 + k) = (st.boolAt "a" k && st.boolAt "b" (i + k % 1))
  known_pp_g_0 : ∀ (i : Nat),
  i < N →
    ∀ (k : Nat),
      k < N →
        (∃ v, st.lookup "pp" = some v ∧ v.width = ((↑N + -1).natAbs + 1) * ((↑N + -1).natAbs + 1)) ∧
          KnownBit st "pp" (rmN (↑N) (↑i) 0 + k)
  stable aliases (copies of the above; same statements):
    eq_pp_1 := eq_pp_g_0    known_pp_1 := known_pp_g_0
  [inRange] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → 0 ≤ i ∧ i ≤ ↑N + -1
  [width] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → (↑N + -1).natAbs + 1 = N
  [bitRead] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → i ≤ ↑(↑N + -1).natAbs
  [cover] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → i < ↑(↑N + -1).natAbs + 1
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (repl_mask.sem N)) (ha : Acyclic (repl_mask.sem N)) (st : SvState)
    (heqs : CombEqs (repl_mask.sem N) st) (hsh : StateShape (repl_mask.sem N) st) : True := by
  sv_equations?
  trivial



/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_y_plain_0 : ∀ (k : Nat), k < Int.natAbs 7 + 1 → st.boolAt "y" k = st.boolAt "x" (k % Int.toNat 2)
  eq_z_plain_1 : ∀ (k : Nat),
  k < Int.natAbs 10 + 1 →
    st.boolAt "z" k =
      if k < Int.toNat 4 * { bits := #[Logic.l0, Logic.l1] }.width + (3 - 2 + 1).toNat then
        if k < (3 - 2 + 1).toNat then st.boolAt "x" (Int.toNat 2 + k)
        else
          { bits := #[Logic.l0, Logic.l1] }.boolAt ((k - (3 - 2 + 1).toNat) % { bits := #[Logic.l0, Logic.l1] }.width)
      else st.boolAt "x" (k - (Int.toNat 4 * { bits := #[Logic.l0, Logic.l1] }.width + (3 - 2 + 1).toNat))
  known_y_plain_0 : ∀ (k : Nat), k < Int.natAbs 7 + 1 → (∃ v, st.lookup "y" = some v ∧ v.width = Int.natAbs 7 + 1) ∧ KnownBit st "y" k
  known_z_plain_1 : ∀ (k : Nat), k < Int.natAbs 10 + 1 → (∃ v, st.lookup "z" = some v ∧ v.width = Int.natAbs 10 + 1) ∧ KnownBit st "z" k
  stable aliases (copies of the above; same statements):
    eq_y_1 := eq_y_plain_0    known_y_1 := known_y_plain_0
    eq_z_1 := eq_z_plain_1    known_z_1 := known_z_plain_1
  decided (flat netlist: every site plain, no parameter): auto, width, bitRead, cover
  [inputsKnown] ⊢ ∃ v, st.lookup "x" = some v ∧ v.allKnown = true ∧ v.width = 8
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (hc : CombDesign (repl_bits.sem)) (ha : Acyclic (repl_bits.sem)) (st : SvState)
    (heqs : CombEqs (repl_bits.sem) st) (hsh : StateShape (repl_bits.sem) st) : True := by
  sv_equations?
  trivial



/--
info: sv_structure: parameters [N, K]
declarations:
  input  x [N - 1 : 0]
  output y [N + K - 1 : 0]
plain sites (module-level assigns):
  plain#0 : drives y   reads [x]
families: none
rank relation a certificate must satisfy (writer < reader whenever the read window
overlaps the written window; ranks are functions of the site identity):
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N K : Nat) (hN : 1 ≤ N) : CombDesign (repl_pad.sem N K) := by
  sv_structure?
  all_goals sorry

/-! ## `*`

A product prints in the form of a sum: `XF.mulBits w f w g k` is bit `k` of `val f w * val g w`, at the CONTEXT width `w`
(the target's), each factor zero-extended to it first (`q`, `2N` bits wide, over two `N`-bit factors). -/

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_p_plain_0 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 →
    st.boolAt "p" k =
      XF.mulBits ((↑N + -1).natAbs + 1) (fun x => st.boolAt "a" x) ((↑N + -1).natAbs + 1) (fun x => st.boolAt "b" x) k
  eq_q_plain_1 : ∀ (k : Nat),
  k < (2 * ↑N + -1).natAbs + 1 →
    st.boolAt "q" k =
      XF.mulBits ((2 * ↑N + -1).natAbs + 1) (fun x => XF.zext ((↑N + -1).natAbs + 1) (fun x => st.boolAt "a" x) x)
        ((2 * ↑N + -1).natAbs + 1) (fun x => XF.zext ((↑N + -1).natAbs + 1) (fun x => st.boolAt "b" x) x) k
  known_p_plain_0 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 → (∃ v, st.lookup "p" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "p" k
  known_q_plain_1 : ∀ (k : Nat),
  k < (2 * ↑N + -1).natAbs + 1 → (∃ v, st.lookup "q" = some v ∧ v.width = (2 * ↑N + -1).natAbs + 1) ∧ KnownBit st "q" k
  stable aliases (copies of the above; same statements):
    eq_p_1 := eq_p_plain_0    known_p_1 := known_p_plain_0
    eq_q_1 := eq_q_plain_1    known_q_1 := known_q_plain_1
  [width] ⊢ (↑N + -1).natAbs ≤ (2 * ↑N + -1).natAbs
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (mul_word.sem N)) (ha : Acyclic (mul_word.sem N)) (st : SvState)
    (heqs : CombEqs (mul_word.sem N) st) (hsh : StateShape (mul_word.sem N) st) : True := by
  sv_equations?
  trivial

end Examples.«system-verilog».comb_word.comb_hint
