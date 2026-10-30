import Examples.«system-verilog».ripple_add.gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombEqTactic

/-!
# `sv_equations?` on the ripple-carry adder

The hint mode prints the netlist view `sv_equations` would hand over (one named hypothesis per
assign, `eq_*` for the Boolean equations and `known_*` for the knownness of the target bits) and the
obligations it returns, and changes nothing. Pinned verbatim: a change of the vocabulary or of the
normal form of the equations is a visible diff here.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».ripple_add.gen

namespace Examples.«system-verilog».ripple_add.comb_hint

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_c_plain_0 : st.boolAt "c" 0 = st.boolAt "cin" 0
  eq_cout_plain_1 : st.boolAt "cout" 0 = st.boolAt "c" N
  eq_s_g_bit_0 : ∀ (i : Nat), i < N → st.boolAt "s" i = (st.boolAt "a" i ^^ st.boolAt "b" i ^^ st.boolAt "c" i)
  eq_c_g_bit_1 : ∀ (i : Nat),
  i < N →
    st.boolAt "c" (i + 1) =
      (st.boolAt "a" i && st.boolAt "b" i || st.boolAt "c" i && (st.boolAt "a" i ^^ st.boolAt "b" i))
  known_c_plain_0 : (∃ v, st.lookup "c" = some v ∧ v.width = N + 1) ∧ KnownBit st "c" 0
  known_cout_plain_1 : (∃ v, st.lookup "cout" = some v ∧ v.width = 1) ∧ KnownBit st "cout" 0
  known_s_g_bit_0 : ∀ (i : Nat), i < N → (∃ v, st.lookup "s" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "s" i
  known_c_g_bit_1 : ∀ (i : Nat), i < N → (∃ v, st.lookup "c" = some v ∧ v.width = N + 1) ∧ KnownBit st "c" (i + 1)
  stable aliases (copies of the above; same statements):
    eq_c_1 := eq_c_plain_0    known_c_1 := known_c_plain_0
    eq_cout_1 := eq_cout_plain_1    known_cout_1 := known_cout_plain_1
    eq_s_1 := eq_s_g_bit_0    known_s_1 := known_s_g_bit_0
    eq_c_2 := eq_c_g_bit_1    known_c_2 := known_c_g_bit_1
  [inRange_1] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → 0 ≤ i ∧ i ≤ ↑(↑N + -1).natAbs
  [inRange_2] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → 0 ≤ i + 1 ∧ i + 1 ≤ ↑N
  [bitRead_1] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → i ≤ ↑(↑N + -1).natAbs ∧ i ≤ ↑N
  [bitRead_2] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → i ≤ ↑(↑N + -1).natAbs ∧ i ≤ ↑N ∧ i ≤ ↑(↑N + -1).natAbs
  [cover_1] ⊢ N = 0 ∨ ∃ i, i < N ∧ ↑i + 1 ≤ ↑N ∧ N < i + 1 + 1
  [cover_2] ⊢ ∀ (i : Int),
  0 ≤ i →
    i < ↑N →
      i < ↑(↑N + -1).natAbs + 1 ∧ (0 ≤ max i 0 ∧ i < 1 ∨ ∃ i_1, i_1 < N ∧ ↑i_1 + 1 ≤ max i 0 ∧ i < max (↑i_1 + 1) 0 + 1)
  [cover_3] ⊢ ∀ (i : Int),
  0 ≤ i →
    i < ↑N →
      i < ↑(↑N + -1).natAbs + 1 ∧
        (0 ≤ max i 0 ∧ i < 1 ∨ ∃ i_1, i_1 < N ∧ ↑i_1 + 1 ≤ max i 0 ∧ i < max (↑i_1 + 1) 0 + 1) ∧
          i < ↑(↑N + -1).natAbs + 1
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_3] ⊢ ∃ v, st.lookup "cin" = some v ∧ v.allKnown = true ∧ v.width = 1
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) :
    ripple_add.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) → True := by
  have hc : CombDesign (ripple_add.sem N) := by sv_structure; all_goals (intros; omega)
  have ha : Acyclic (ripple_add.sem N) := by
    sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y ci hA hB hCi
  sv_equations?
  trivial

end Examples.«system-verilog».ripple_add.comb_hint
