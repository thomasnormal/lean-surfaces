import Examples.«system-verilog».lp_add.gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombEqTactic

/-!
# `sv_equations?` on the ripple-carry adder with localparams

The hint mode prints the netlist view `sv_equations` hands over for `lp_add.sv` and the obligations it
returns. A localparam is inlined by its definition (`T` is `2 * ((↑N + 1) / 2) - ↑N % 2`: `/` and `%`
by a literal, floor division, which `omega` reads; the truncating `Int.tdiv`/`Int.tmod` of the
elaborated design were rewritten under the hypothesis `hN`), and `c[M + 1]` with `M = N - 1` is
already `c N`. Pinned verbatim, as `ripple_add/comb_hint.lean` pins the localparam-free adder: a
change of the vocabulary or of the normal form of the equations is a visible diff here.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».lp_add.gen

namespace Examples.«system-verilog».lp_add.comb_hint

/--
info: sv_equations: the netlist view and the obligations
  eq_c_plain_0 : st.boolAt "c" 0 = st.boolAt "cin" 0
  eq_cout_plain_1 : st.boolAt "cout" 0 = st.boolAt "c" N
  eq_s_g_bit_0 : ∀ (i : Nat),
  ↑i < 2 * ((↑N + 1) / 2) - ↑N % 2 → st.boolAt "s" i = (st.boolAt "a" i ^^ st.boolAt "b" i ^^ st.boolAt "c" i)
  eq_c_g_bit_1 : ∀ (i : Nat),
  ↑i < 2 * ((↑N + 1) / 2) - ↑N % 2 →
    st.boolAt "c" (i + 1) =
      (st.boolAt "a" i && st.boolAt "b" i || st.boolAt "c" i && (st.boolAt "a" i ^^ st.boolAt "b" i))
  known_c_plain_0 : (∃ v, st.lookup "c" = some v ∧ v.width = (2 * ((↑N + 1) / 2) - ↑N % 2).natAbs + 1) ∧ KnownBit st "c" 0
  known_cout_plain_1 : (∃ v, st.lookup "cout" = some v ∧ v.width = 1) ∧ KnownBit st "cout" 0
  known_s_g_bit_0 : ∀ (i : Nat),
  ↑i < 2 * ((↑N + 1) / 2) - ↑N % 2 → (∃ v, st.lookup "s" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "s" i
  known_c_g_bit_1 : ∀ (i : Nat),
  ↑i < 2 * ((↑N + 1) / 2) - ↑N % 2 →
    (∃ v, st.lookup "c" = some v ∧ v.width = (2 * ((↑N + 1) / 2) - ↑N % 2).natAbs + 1) ∧ KnownBit st "c" (i + 1)
  [inRange_1] ⊢ ↑N % 2 ≤ 2 * ((↑N + 1) / 2)
  [inRange_2] ⊢ ∀ (i : Int), 0 ≤ i → i < 2 * ((↑N + 1) / 2) - ↑N % 2 → 0 ≤ i ∧ i ≤ ↑(↑N + -1).natAbs
  [inRange_3] ⊢ ∀ (i : Int), 0 ≤ i → i < 2 * ((↑N + 1) / 2) - ↑N % 2 → 0 ≤ i + 1 ∧ i + 1 ≤ ↑(2 * ((↑N + 1) / 2) - ↑N % 2).natAbs
  [bitRead_1] ⊢ ∀ (i : Int), 0 ≤ i → i < 2 * ((↑N + 1) / 2) - ↑N % 2 → i ≤ ↑(↑N + -1).natAbs ∧ i ≤ ↑(2 * ((↑N + 1) / 2) - ↑N % 2).natAbs
  [bitRead_2] ⊢ ∀ (i : Int),
  0 ≤ i →
    i < 2 * ((↑N + 1) / 2) - ↑N % 2 →
      i ≤ ↑(↑N + -1).natAbs ∧ i ≤ ↑(2 * ((↑N + 1) / 2) - ↑N % 2).natAbs ∧ i ≤ ↑(↑N + -1).natAbs
  [cover_1] ⊢ N = 0 ∨ ∃ i, ↑i < 2 * ((↑N + 1) / 2) - ↑N % 2 ∧ ↑i + 1 ≤ ↑N ∧ N < i + 1 + 1
  [cover_2] ⊢ ∀ (i : Int),
  0 ≤ i →
    i < 2 * ((↑N + 1) / 2) - ↑N % 2 →
      i < ↑(↑N + -1).natAbs + 1 ∧
        (0 ≤ max i 0 ∧ i < 1 ∨
          ∃ i_1, ↑i_1 < 2 * ((↑N + 1) / 2) - ↑N % 2 ∧ ↑i_1 + 1 ≤ max i 0 ∧ i < max (↑i_1 + 1) 0 + 1)
  [cover_3] ⊢ ∀ (i : Int),
  0 ≤ i →
    i < 2 * ((↑N + 1) / 2) - ↑N % 2 →
      i < ↑(↑N + -1).natAbs + 1 ∧
        (0 ≤ max i 0 ∧ i < 1 ∨
            ∃ i_1, ↑i_1 < 2 * ((↑N + 1) / 2) - ↑N % 2 ∧ ↑i_1 + 1 ≤ max i 0 ∧ i < max (↑i_1 + 1) 0 + 1) ∧
          i < ↑(↑N + -1).natAbs + 1
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_3] ⊢ ∃ v, st.lookup "cin" = some v ∧ v.allKnown = true ∧ v.width = 1
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) :
    lp_add.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) → True := by
  have hc : CombDesign (lp_add.sem N) := by sv_structure; all_goals (intros; omega)
  have ha : Acyclic (lp_add.sem N) := by
    sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
    all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y ci hA hB hCi
  sv_equations?
  trivial

end Examples.«system-verilog».lp_add.comb_hint
