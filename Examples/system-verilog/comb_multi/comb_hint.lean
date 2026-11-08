import Examples.«system-verilog».comb_multi.gen
import LeanModels.Sv.CombProcTactic

/-!
# `sv_equations?` on a body that writes several windows (WP-G S1b, gate d)

The hint mode prints the netlist view `sv_equations` would hand over and the obligations it returns, and changes
nothing. A body that writes several windows has ONE fact per window, in this order: the head window of every site
under the names of the single-window route (`eq_<signal>_<block>_<position>`), then the further windows of each site
named after their own signal with `_w<j>` (`eq_s_g_bit_1_w1`). The stable aliases (`eq_<signal>_<k>`) count the
WINDOWS that write each signal, in source order, so the whole carry/sum cell in one body has the SAME aliases and the
SAME statements as `add_proc`'s separate carry cell and sum assign (`comb_proc/comb_hint.lean`): `eq_c_2` is the
carry cell, `eq_s_1` the sum. Pinned verbatim: a change of the vocabulary or of the normal form is a visible diff
here. `multi_same` writes two windows of ONE signal in one body: the aliases `eq_y_1`, `eq_y_2` follow source order, and
the obligation that the two windows are disjoint is closed by the normalizer (no `within` goal). This file REPLACES the
refusal pins of gate c (`sv_equations` refused such a body before gate d).
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».comb_multi.gen

namespace Examples.«system-verilog».comb_multi.comb_hint

/--
info: sv_equations: the netlist view and the obligations (lowered design)
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_c_plain_0 : st.boolAt "c" 0 = st.boolAt "cin" 0
  eq_cout_plain_1 : st.boolAt "cout" 0 = st.boolAt "c" N
  eq_p_g_bit_0 : ∀ (i : Nat), i < N → st.boolAt "p" i = (st.boolAt "a" i ^^ st.boolAt "b" i)
  eq_c_g_bit_1 : ∀ (i : Nat), i < N → st.boolAt "c" (i + 1) = if st.boolAt "p" i = true then st.boolAt "c" i else st.boolAt "a" i
  eq_s_g_bit_1_w1 : ∀ (i : Nat), i < N → st.boolAt "s" i = (st.boolAt "p" i ^^ st.boolAt "c" i)
  known_c_plain_0 : (∃ v, st.lookup "c" = some v ∧ v.width = N + 1) ∧ KnownBit st "c" 0
  known_cout_plain_1 : (∃ v, st.lookup "cout" = some v ∧ v.width = 1) ∧ KnownBit st "cout" 0
  known_p_g_bit_0 : ∀ (i : Nat), i < N → (∃ v, st.lookup "p" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "p" i
  known_c_g_bit_1 : ∀ (i : Nat), i < N → (∃ v, st.lookup "c" = some v ∧ v.width = N + 1) ∧ KnownBit st "c" (i + 1)
  known_s_g_bit_1_w1 : ∀ (i : Nat), i < N → (∃ v, st.lookup "s" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "s" i
  stable aliases (copies of the above; same statements):
    eq_c_1 := eq_c_plain_0    known_c_1 := known_c_plain_0
    eq_cout_1 := eq_cout_plain_1    known_cout_1 := known_cout_plain_1
    eq_p_1 := eq_p_g_bit_0    known_p_1 := known_p_g_bit_0
    eq_c_2 := eq_c_g_bit_1    known_c_2 := known_c_g_bit_1
    eq_s_1 := eq_s_g_bit_1_w1    known_s_1 := known_s_g_bit_1_w1
  [inRange_1] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → 0 ≤ i ∧ i ≤ ↑(↑N + -1).natAbs
  [inRange_2] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → 0 ≤ i + 1 ∧ i + 1 ≤ ↑N
  [inRange_3] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → 0 ≤ i ∧ i ≤ ↑(↑N + -1).natAbs
  [noSelfRead] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → (i + 1).toNat + 1 ≤ i.toNat ∨ i.toNat + 1 ≤ (i + 1).toNat
  [bitRead_1] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → i ≤ ↑(↑N + -1).natAbs
  [bitRead_2] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → i ≤ ↑(↑N + -1).natAbs ∧ i ≤ ↑N ∧ i ≤ ↑(↑N + -1).natAbs ∧ i ≤ ↑N
  [cover_1] ⊢ N = 0 ∨ ∃ i, i < N ∧ ↑i + 1 ≤ ↑N ∧ N < i + 1 + 1
  [cover_2] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → i < ↑(↑N + -1).natAbs + 1
  [cover_3] ⊢ ∀ (i : Int),
  0 ≤ i →
    i < ↑N →
      (∃ i_1, i_1 < N ∧ ↑i_1 ≤ max i 0 ∧ i < ↑i_1 + 1) ∧
        (0 ≤ max i 0 ∧ i < 1 ∨ ∃ i_1, i_1 < N ∧ ↑i_1 + 1 ≤ max i 0 ∧ i < max (↑i_1 + 1) 0 + 1) ∧
          i < ↑(↑N + -1).natAbs + 1 ∧
            (∃ i_1, i_1 < N ∧ ↑i_1 ≤ max i 0 ∧ i < ↑i_1 + 1) ∧
              (0 ≤ max i 0 ∧ i < 1 ∨ ∃ i_1, i_1 < N ∧ ↑i_1 + 1 ≤ max i 0 ∧ i < max (↑i_1 + 1) 0 + 1)
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_3] ⊢ ∃ v, st.lookup "cin" = some v ∧ v.allKnown = true ∧ v.width = 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648)
    {d' : Design2} (hl : (add_proc_m.sem N).lowerComb = some d')
    (hc : CombDesign d') (ha : Acyclic d') (st : SvState) (heqs : CombEqs d' st)
    (hsh : StateShape d' st) : True := by
  sv_equations?
  trivial

/--
info: sv_equations: the netlist view and the obligations (lowered design)
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_y_plain_0 : ∀ (k : Nat),
  k < Int.natAbs 3 + 1 → st.boolAt "y" k = if st.boolAt "e" 0 = true then st.boolAt "b" k else st.boolAt "a" k
  eq_z_plain_0_w1 : ∀ (k : Nat), k < Int.natAbs 3 + 1 → st.boolAt "z" k = (st.boolAt "a" k ^^ st.boolAt "b" k)
  known_y_plain_0 : ∀ (k : Nat), k < Int.natAbs 3 + 1 → (∃ v, st.lookup "y" = some v ∧ v.width = Int.natAbs 3 + 1) ∧ KnownBit st "y" k
  known_z_plain_0_w1 : ∀ (k : Nat), k < Int.natAbs 3 + 1 → (∃ v, st.lookup "z" = some v ∧ v.width = Int.natAbs 3 + 1) ∧ KnownBit st "z" k
  stable aliases (copies of the above; same statements):
    eq_y_1 := eq_y_plain_0    known_y_1 := known_y_plain_0
    eq_z_1 := eq_z_plain_0_w1    known_z_1 := known_z_plain_0_w1
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = 4
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = 4
  [inputsKnown_3] ⊢ ∃ v, st.lookup "e" = some v ∧ v.allKnown = true ∧ v.width = 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example {d' : Design2} (hl : multi_flat.sem.lowerComb = some d')
    (hc : CombDesign d') (ha : Acyclic d') (st : SvState) (heqs : CombEqs d' st)
    (hsh : StateShape d' st) : True := by
  sv_equations?
  trivial

/--
info: sv_equations: the netlist view and the obligations (lowered design)
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_y_plain_0 : st.boolAt "y" 0 = (st.boolAt "a" 0 && st.boolAt "b" 0)
  eq_y_plain_0_w1 : st.boolAt "y" (Int.toNat 1) = (st.boolAt "a" (Int.toNat 1) || st.boolAt "b" (Int.toNat 1))
  known_y_plain_0 : (∃ v, st.lookup "y" = some v ∧ v.width = Int.natAbs 1 + 1) ∧ KnownBit st "y" 0
  known_y_plain_0_w1 : (∃ v, st.lookup "y" = some v ∧ v.width = Int.natAbs 1 + 1) ∧ KnownBit st "y" (Int.toNat 1)
  stable aliases (copies of the above; same statements):
    eq_y_1 := eq_y_plain_0    known_y_1 := known_y_plain_0
    eq_y_2 := eq_y_plain_0_w1    known_y_2 := known_y_plain_0_w1
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = 2
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = 2
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example {d' : Design2} (hl : multi_same.sem.lowerComb = some d')
    (hc : CombDesign d') (ha : Acyclic d') (st : SvState) (heqs : CombEqs d' st)
    (hsh : StateShape d' st) : True := by
  sv_equations?
  trivial

end Examples.«system-verilog».comb_multi.comb_hint
