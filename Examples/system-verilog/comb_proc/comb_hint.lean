import Examples.«system-verilog».comb_proc.gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombProcTactic

/-!
# `sv_equations?` on the ripple-carry adder with an `always_comb` carry cell

The hint mode prints the netlist view `sv_equations` would hand over and the obligations it returns, and
changes nothing. The carry cell's equation is the body's own: an `if` on the first bit of the condition
(`eq_c_g_bit_1`). Pinned verbatim: a change of the vocabulary or of the normal form is a visible diff here.
The hypotheses are those of the lowered shape: `hl : (add_proc.sem N).lowerComb = some d'` and the settled
state of `d'`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».comb_proc.gen

namespace Examples.«system-verilog».comb_proc.comb_hint

/--
info: sv_equations: the netlist view and the obligations (lowered design)
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_c_plain_0 : st.boolAt "c" 0 = st.boolAt "cin" 0
  eq_cout_plain_1 : st.boolAt "cout" 0 = st.boolAt "c" N
  eq_p_g_bit_0 : ∀ (i : Nat), i < N → st.boolAt "p" i = (st.boolAt "a" i ^^ st.boolAt "b" i)
  eq_c_g_bit_1 : ∀ (i : Nat), i < N → st.boolAt "c" (i + 1) = if st.boolAt "p" i = true then st.boolAt "c" i else st.boolAt "a" i
  eq_s_g_bit_2 : ∀ (i : Nat), i < N → st.boolAt "s" i = (st.boolAt "p" i ^^ st.boolAt "c" i)
  known_c_plain_0 : (∃ v, st.lookup "c" = some v ∧ v.width = N + 1) ∧ KnownBit st "c" 0
  known_cout_plain_1 : (∃ v, st.lookup "cout" = some v ∧ v.width = 1) ∧ KnownBit st "cout" 0
  known_p_g_bit_0 : ∀ (i : Nat), i < N → (∃ v, st.lookup "p" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "p" i
  known_c_g_bit_1 : ∀ (i : Nat), i < N → (∃ v, st.lookup "c" = some v ∧ v.width = N + 1) ∧ KnownBit st "c" (i + 1)
  known_s_g_bit_2 : ∀ (i : Nat), i < N → (∃ v, st.lookup "s" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "s" i
  stable aliases (copies of the above; same statements):
    eq_c_1 := eq_c_plain_0    known_c_1 := known_c_plain_0
    eq_cout_1 := eq_cout_plain_1    known_cout_1 := known_cout_plain_1
    eq_p_1 := eq_p_g_bit_0    known_p_1 := known_p_g_bit_0
    eq_c_2 := eq_c_g_bit_1    known_c_2 := known_c_g_bit_1
    eq_s_1 := eq_s_g_bit_2    known_s_1 := known_s_g_bit_2
  [inRange_1] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → 0 ≤ i ∧ i ≤ ↑(↑N + -1).natAbs
  [inRange_2] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → 0 ≤ i + 1 ∧ i + 1 ≤ ↑N
  [inRange_3] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → 0 ≤ i ∧ i ≤ ↑(↑N + -1).natAbs
  [noSelfRead] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → (i + 1).toNat + 1 ≤ i.toNat ∨ i.toNat + 1 ≤ (i + 1).toNat
  [bitRead_1] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → i ≤ ↑(↑N + -1).natAbs
  [bitRead_2] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → i ≤ ↑(↑N + -1).natAbs ∧ i ≤ ↑N ∧ i ≤ ↑(↑N + -1).natAbs
  [bitRead_3] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → i ≤ ↑(↑N + -1).natAbs ∧ i ≤ ↑N
  [cover_1] ⊢ N = 0 ∨ ∃ i, i < N ∧ ↑i + 1 ≤ ↑N ∧ N < i + 1 + 1
  [cover_2] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → i < ↑(↑N + -1).natAbs + 1
  [cover_3] ⊢ ∀ (i : Int),
  0 ≤ i →
    i < ↑N →
      (∃ i_1, i_1 < N ∧ ↑i_1 ≤ max i 0 ∧ i < ↑i_1 + 1) ∧
        (0 ≤ max i 0 ∧ i < 1 ∨ ∃ i_1, i_1 < N ∧ ↑i_1 + 1 ≤ max i 0 ∧ i < max (↑i_1 + 1) 0 + 1) ∧
          i < ↑(↑N + -1).natAbs + 1
  [cover_4] ⊢ ∀ (i : Int),
  0 ≤ i →
    i < ↑N →
      (∃ i_1, i_1 < N ∧ ↑i_1 ≤ max i 0 ∧ i < ↑i_1 + 1) ∧
        (0 ≤ max i 0 ∧ i < 1 ∨ ∃ i_1, i_1 < N ∧ ↑i_1 + 1 ≤ max i 0 ∧ i < max (↑i_1 + 1) 0 + 1)
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_3] ⊢ ∃ v, st.lookup "cin" = some v ∧ v.allKnown = true ∧ v.width = 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) {d' : Design2} (hl : (add_proc.sem N).lowerComb = some d')
    (hc : CombDesign d') (ha : Acyclic d') (st : SvState) (heqs : CombEqs d' st)
    (hsh : StateShape d' st) : True := by
  sv_equations?
  trivial

end Examples.«system-verilog».comb_proc.comb_hint
