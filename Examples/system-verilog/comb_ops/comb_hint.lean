import Examples.«system-verilog».comb_ops.gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombProcTactic

/-!
# `sv_equations?` on designs with the new operators (WP-G S2)

What the player sees. The conditional expression `c ? a : b` prints exactly like the `if` of an `always_comb`
(`if <condition bit 0> = true then … else …`), `~` is `!` over `Bool`, a reduction is `XF.any` (or
`XF.all` / `XF.parity`, negated for the `~` forms) over the bits of its operand, `!` of a vector is
`!XF.any …`, `&&` and `||` are `Bool` `&&` and `||` over `XF.any` of their operands, and `==` is
`XF.eqv`. For one-bit operands `XF.any 1 f` is `f 0` and `XF.eqv 1 f g` is `decide (f 0 = g 0)`. Pinned verbatim.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».comb_ops.gen

namespace Examples.«system-verilog».comb_ops.comb_hint

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_c_plain_0 : st.boolAt "c" 0 = st.boolAt "cin" 0
  eq_cout_plain_1 : st.boolAt "cout" 0 = st.boolAt "c" N
  eq_e_g_bit_0 : ∀ (i : Nat), i < N → st.boolAt "e" i = !(st.boolAt "a" i ^^ st.boolAt "b" i)
  eq_c_g_bit_1 : ∀ (i : Nat), i < N → st.boolAt "c" (i + 1) = if st.boolAt "e" i = true then st.boolAt "a" i else st.boolAt "c" i
  eq_s_g_bit_2 : ∀ (i : Nat), i < N → st.boolAt "s" i = !(st.boolAt "e" i ^^ st.boolAt "c" i)
  known_c_plain_0 : (∃ v, st.lookup "c" = some v ∧ v.width = N + 1) ∧ KnownBit st "c" 0
  known_cout_plain_1 : (∃ v, st.lookup "cout" = some v ∧ v.width = 1) ∧ KnownBit st "cout" 0
  known_e_g_bit_0 : ∀ (i : Nat), i < N → (∃ v, st.lookup "e" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "e" i
  known_c_g_bit_1 : ∀ (i : Nat), i < N → (∃ v, st.lookup "c" = some v ∧ v.width = N + 1) ∧ KnownBit st "c" (i + 1)
  known_s_g_bit_2 : ∀ (i : Nat), i < N → (∃ v, st.lookup "s" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "s" i
  stable aliases (copies of the above; same statements):
    eq_c_1 := eq_c_plain_0    known_c_1 := known_c_plain_0
    eq_cout_1 := eq_cout_plain_1    known_cout_1 := known_cout_plain_1
    eq_e_1 := eq_e_g_bit_0    known_e_1 := known_e_g_bit_0
    eq_c_2 := eq_c_g_bit_1    known_c_2 := known_c_g_bit_1
    eq_s_1 := eq_s_g_bit_2    known_s_1 := known_s_g_bit_2
  [inRange_1] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → 0 ≤ i ∧ i ≤ ↑(↑N + -1).natAbs
  [inRange_2] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → 0 ≤ i + 1 ∧ i + 1 ≤ ↑N
  [inRange_3] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → 0 ≤ i ∧ i ≤ ↑(↑N + -1).natAbs
  [bitRead_1] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → i ≤ ↑(↑N + -1).natAbs
  [bitRead_2] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → i ≤ ↑(↑N + -1).natAbs ∧ i ≤ ↑N
  [cover_1] ⊢ N = 0 ∨ ∃ i, i < N ∧ ↑i + 1 ≤ ↑N ∧ N < i + 1 + 1
  [cover_2] ⊢ ∀ (i : Int), 0 ≤ i → i < ↑N → i < ↑(↑N + -1).natAbs + 1
  [cover_3] ⊢ ∀ (i : Int),
  0 ≤ i →
    i < ↑N →
      (∃ i_1, i_1 < N ∧ ↑i_1 ≤ max i 0 ∧ i < ↑i_1 + 1) ∧
        i < ↑(↑N + -1).natAbs + 1 ∧
          (0 ≤ max i 0 ∧ i < 1 ∨ ∃ i_1, i_1 < N ∧ ↑i_1 + 1 ≤ max i 0 ∧ i < max (↑i_1 + 1) 0 + 1)
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
example (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (add_mux.sem N)) (ha : Acyclic (add_mux.sem N))
    (st : SvState) (heqs : CombEqs (add_mux.sem N) st) (hsh : StateShape (add_mux.sem N) st) :
    True := by
  sv_equations?
  trivial

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_y_not_plain_0 : ∀ (k : Nat), k < (↑N + -1).natAbs + 1 → st.boolAt "y_not" k = !st.boolAt "a" k
  eq_y_mux_plain_1 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 → st.boolAt "y_mux" k = if st.boolAt "s" 0 = true then st.boolAt "a" k else st.boolAt "b" k
  eq_y_xnor_plain_2 : ∀ (k : Nat), k < (↑N + -1).natAbs + 1 → st.boolAt "y_xnor" k = !(st.boolAt "a" k ^^ st.boolAt "b" k)
  eq_y_nest_plain_3 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 →
    st.boolAt "y_nest" k =
      if st.boolAt "s" 0 = true then !st.boolAt "a" k
      else if st.boolAt "a" 0 = true then st.boolAt "b" k else st.boolAt "a" k
  eq_r_or_plain_4 : st.boolAt "r_or" 0 = XF.any ((↑N + -1).natAbs + 1) fun x => st.boolAt "a" x
  eq_r_and_plain_5 : st.boolAt "r_and" 0 = XF.all ((↑N + -1).natAbs + 1) fun x => st.boolAt "b" x
  eq_r_xor_plain_6 : st.boolAt "r_xor" 0 = XF.parity ((↑N + -1).natAbs + 1) fun x => st.boolAt "a" x
  eq_r_nor_plain_7 : st.boolAt "r_nor" 0 = !XF.any ((↑N + -1).natAbs + 1) fun x => st.boolAt "b" x
  eq_r_nand_plain_8 : st.boolAt "r_nand" 0 = !XF.all ((↑N + -1).natAbs + 1) fun x => st.boolAt "a" x
  eq_r_xnor_plain_9 : st.boolAt "r_xnor" 0 = !XF.parity ((↑N + -1).natAbs + 1) fun x => st.boolAt "b" x
  eq_z_lnot_plain_10 : st.boolAt "z_lnot" 0 = !XF.any ((↑N + -1).natAbs + 1) fun x => st.boolAt "b" x
  eq_q_land_plain_11 : st.boolAt "q_land" 0 = (st.boolAt "s" 0 && st.boolAt "a" 0)
  eq_q_lor_plain_12 : st.boolAt "q_lor" 0 = (st.boolAt "a" 0 || !st.boolAt "b" 0)
  eq_q_eq_plain_13 : st.boolAt "q_eq" 0 = XF.eqv ((↑N + -1).natAbs + 1) (fun x => st.boolAt "a" x) fun x => st.boolAt "b" x
  eq_q_ne_plain_14 : st.boolAt "q_ne" 0 = !decide (st.boolAt "a" 0 = st.boolAt "b" 0)
  eq_q_cond_plain_15 : st.boolAt "q_cond" 0 =
  if (st.boolAt "a" 0 ^^ st.boolAt "b" 0) = true then XF.all ((↑N + -1).natAbs + 1) fun x => st.boolAt "a" x
  else !XF.any ((↑N + -1).natAbs + 1) fun x => st.boolAt "b" x
  known_y_not_plain_0 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 → (∃ v, st.lookup "y_not" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "y_not" k
  known_y_mux_plain_1 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 → (∃ v, st.lookup "y_mux" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "y_mux" k
  known_y_xnor_plain_2 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 →
    (∃ v, st.lookup "y_xnor" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "y_xnor" k
  known_y_nest_plain_3 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 →
    (∃ v, st.lookup "y_nest" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "y_nest" k
  known_r_or_plain_4 : (∃ v, st.lookup "r_or" = some v ∧ v.width = 1) ∧ KnownBit st "r_or" 0
  known_r_and_plain_5 : (∃ v, st.lookup "r_and" = some v ∧ v.width = 1) ∧ KnownBit st "r_and" 0
  known_r_xor_plain_6 : (∃ v, st.lookup "r_xor" = some v ∧ v.width = 1) ∧ KnownBit st "r_xor" 0
  known_r_nor_plain_7 : (∃ v, st.lookup "r_nor" = some v ∧ v.width = 1) ∧ KnownBit st "r_nor" 0
  known_r_nand_plain_8 : (∃ v, st.lookup "r_nand" = some v ∧ v.width = 1) ∧ KnownBit st "r_nand" 0
  known_r_xnor_plain_9 : (∃ v, st.lookup "r_xnor" = some v ∧ v.width = 1) ∧ KnownBit st "r_xnor" 0
  known_z_lnot_plain_10 : (∃ v, st.lookup "z_lnot" = some v ∧ v.width = 1) ∧ KnownBit st "z_lnot" 0
  known_q_land_plain_11 : (∃ v, st.lookup "q_land" = some v ∧ v.width = 1) ∧ KnownBit st "q_land" 0
  known_q_lor_plain_12 : (∃ v, st.lookup "q_lor" = some v ∧ v.width = 1) ∧ KnownBit st "q_lor" 0
  known_q_eq_plain_13 : (∃ v, st.lookup "q_eq" = some v ∧ v.width = 1) ∧ KnownBit st "q_eq" 0
  known_q_ne_plain_14 : (∃ v, st.lookup "q_ne" = some v ∧ v.width = 1) ∧ KnownBit st "q_ne" 0
  known_q_cond_plain_15 : (∃ v, st.lookup "q_cond" = some v ∧ v.width = 1) ∧ KnownBit st "q_cond" 0
  stable aliases (copies of the above; same statements):
    eq_y_not_1 := eq_y_not_plain_0    known_y_not_1 := known_y_not_plain_0
    eq_y_mux_1 := eq_y_mux_plain_1    known_y_mux_1 := known_y_mux_plain_1
    eq_y_xnor_1 := eq_y_xnor_plain_2    known_y_xnor_1 := known_y_xnor_plain_2
    eq_y_nest_1 := eq_y_nest_plain_3    known_y_nest_1 := known_y_nest_plain_3
    eq_r_or_1 := eq_r_or_plain_4    known_r_or_1 := known_r_or_plain_4
    eq_r_and_1 := eq_r_and_plain_5    known_r_and_1 := known_r_and_plain_5
    eq_r_xor_1 := eq_r_xor_plain_6    known_r_xor_1 := known_r_xor_plain_6
    eq_r_nor_1 := eq_r_nor_plain_7    known_r_nor_1 := known_r_nor_plain_7
    eq_r_nand_1 := eq_r_nand_plain_8    known_r_nand_1 := known_r_nand_plain_8
    eq_r_xnor_1 := eq_r_xnor_plain_9    known_r_xnor_1 := known_r_xnor_plain_9
    eq_z_lnot_1 := eq_z_lnot_plain_10    known_z_lnot_1 := known_z_lnot_plain_10
    eq_q_land_1 := eq_q_land_plain_11    known_q_land_1 := known_q_land_plain_11
    eq_q_lor_1 := eq_q_lor_plain_12    known_q_lor_1 := known_q_lor_plain_12
    eq_q_eq_1 := eq_q_eq_plain_13    known_q_eq_1 := known_q_eq_plain_13
    eq_q_ne_1 := eq_q_ne_plain_14    known_q_ne_1 := known_q_ne_plain_14
    eq_q_cond_1 := eq_q_cond_plain_15    known_q_cond_1 := known_q_cond_plain_15
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_3] ⊢ ∃ v, st.lookup "s" = some v ∧ v.allKnown = true ∧ v.width = 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (ops_gen.sem N)) (ha : Acyclic (ops_gen.sem N))
    (st : SvState) (heqs : CombEqs (ops_gen.sem N) st) (hsh : StateShape (ops_gen.sem N) st) :
    True := by
  sv_equations?
  trivial

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_n_plain_0 : ∀ (k : Nat), k < Int.natAbs 3 + 1 → st.boolAt "n" k = !(st.boolAt "a" k ^^ st.boolAt "b" k)
  eq_w_plain_1 : st.boolAt "w" 0 = !(st.boolAt "s" 0 && st.boolAt "t" 0)
  eq_y_plain_2 : ∀ (k : Nat),
  k < Int.natAbs 3 + 1 →
    st.boolAt "y" k = if st.boolAt "w" 0 = true then st.boolAt "n" k else st.boolAt "a" k && st.boolAt "b" k
  eq_z_plain_3 : ∀ (k : Nat),
  k < Int.natAbs 3 + 1 → st.boolAt "z" k = if st.boolAt "s" 0 = true then !st.boolAt "a" k else st.boolAt "b" k
  eq_p_plain_4 : st.boolAt "p" 0 = XF.any (Int.natAbs 3 + 1) fun x => st.boolAt "y" x
  eq_q_plain_5 : st.boolAt "q" 0 =
  ((XF.eqv (Int.natAbs 3 + 1) (fun x => st.boolAt "a" x) fun x => st.boolAt "b" x) ||
    !decide (st.boolAt "s" 0 = st.boolAt "t" 0))
  eq_r_plain_6 : st.boolAt "r" 0 = XF.all (Int.natAbs 3 + 1) fun x => st.boolAt "n" x
  eq_u_plain_7 : st.boolAt "u" 0 = !XF.parity (Int.natAbs 3 + 1) fun x => st.boolAt "z" x
  known_n_plain_0 : ∀ (k : Nat), k < Int.natAbs 3 + 1 → (∃ v, st.lookup "n" = some v ∧ v.width = Int.natAbs 3 + 1) ∧ KnownBit st "n" k
  known_w_plain_1 : (∃ v, st.lookup "w" = some v ∧ v.width = 1) ∧ KnownBit st "w" 0
  known_y_plain_2 : ∀ (k : Nat), k < Int.natAbs 3 + 1 → (∃ v, st.lookup "y" = some v ∧ v.width = Int.natAbs 3 + 1) ∧ KnownBit st "y" k
  known_z_plain_3 : ∀ (k : Nat), k < Int.natAbs 3 + 1 → (∃ v, st.lookup "z" = some v ∧ v.width = Int.natAbs 3 + 1) ∧ KnownBit st "z" k
  known_p_plain_4 : (∃ v, st.lookup "p" = some v ∧ v.width = 1) ∧ KnownBit st "p" 0
  known_q_plain_5 : (∃ v, st.lookup "q" = some v ∧ v.width = 1) ∧ KnownBit st "q" 0
  known_r_plain_6 : (∃ v, st.lookup "r" = some v ∧ v.width = 1) ∧ KnownBit st "r" 0
  known_u_plain_7 : (∃ v, st.lookup "u" = some v ∧ v.width = 1) ∧ KnownBit st "u" 0
  stable aliases (copies of the above; same statements):
    eq_n_1 := eq_n_plain_0    known_n_1 := known_n_plain_0
    eq_w_1 := eq_w_plain_1    known_w_1 := known_w_plain_1
    eq_y_1 := eq_y_plain_2    known_y_1 := known_y_plain_2
    eq_z_1 := eq_z_plain_3    known_z_1 := known_z_plain_3
    eq_p_1 := eq_p_plain_4    known_p_1 := known_p_plain_4
    eq_q_1 := eq_q_plain_5    known_q_1 := known_q_plain_5
    eq_r_1 := eq_r_plain_6    known_r_1 := known_r_plain_6
    eq_u_1 := eq_u_plain_7    known_u_1 := known_u_plain_7
  decided (flat netlist: every site plain, no parameter): auto, inRange, width, bitRead, cover
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = 4
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = 4
  [inputsKnown_3] ⊢ ∃ v, st.lookup "s" = some v ∧ v.allKnown = true ∧ v.width = 1
  [inputsKnown_4] ⊢ ∃ v, st.lookup "t" = some v ∧ v.allKnown = true ∧ v.width = 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (hc : CombDesign ops_flat.sem) (ha : Acyclic ops_flat.sem)
    (st : SvState) (heqs : CombEqs ops_flat.sem st) (hsh : StateShape ops_flat.sem st) : True := by
  sv_equations?
  trivial

/--
info: sv_equations: the netlist view and the obligations (lowered design)
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_p_plain_0 : ∀ (k : Nat), k < (↑N + -1).natAbs + 1 → st.boolAt "p" k = (st.boolAt "a" k ^^ st.boolAt "b" k)
  eq_z_plain_1 : ∀ (k : Nat), k < (↑N + -1).natAbs + 1 → st.boolAt "z" k = !st.boolAt "p" k
  eq_y_plain_2 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 →
    st.boolAt "y" k =
      if (!st.boolAt "p" 0 && (st.boolAt "a" 0 || st.boolAt "b" 0)) = true then !st.boolAt "a" k
      else
        if (XF.any ((↑N + -1).natAbs + 1) fun x => st.boolAt "v" x) = true then st.boolAt "b" k
        else
          if (XF.eqv ((↑N + -1).natAbs + 1) (fun x => st.boolAt "a" x) fun x => st.boolAt "b" x) = true then
            st.boolAt "a" k
          else st.boolAt "v" k
  eq_w_plain_3 : st.boolAt "w" 0 =
  if decide (st.boolAt "a" 0 = st.boolAt "b" 0) = true then XF.all ((↑N + -1).natAbs + 1) fun x => st.boolAt "v" x
  else if (!st.boolAt "a" 0) = true then !st.boolAt "b" 0 else st.boolAt "v" 0
  known_p_plain_0 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 → (∃ v, st.lookup "p" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "p" k
  known_z_plain_1 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 → (∃ v, st.lookup "z" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "z" k
  known_y_plain_2 : ∀ (k : Nat),
  k < (↑N + -1).natAbs + 1 → (∃ v, st.lookup "y" = some v ∧ v.width = (↑N + -1).natAbs + 1) ∧ KnownBit st "y" k
  known_w_plain_3 : (∃ v, st.lookup "w" = some v ∧ v.width = 1) ∧ KnownBit st "w" 0
  stable aliases (copies of the above; same statements):
    eq_p_1 := eq_p_plain_0    known_p_1 := known_p_plain_0
    eq_z_1 := eq_z_plain_1    known_z_1 := known_z_plain_1
    eq_y_1 := eq_y_plain_2    known_y_1 := known_y_plain_2
    eq_w_1 := eq_w_plain_3    known_w_1 := known_w_plain_3
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
  [inputsKnown_3] ⊢ ∃ v, st.lookup "v" = some v ∧ v.allKnown = true ∧ v.width = (↑N + -1).natAbs + 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) {d' : Design2} (hl : (ops_proc.sem N).lowerComb = some d')
    (hc : CombDesign d') (ha : Acyclic d') (st : SvState) (heqs : CombEqs d' st)
    (hsh : StateShape d' st) : True := by
  sv_equations?
  trivial

end Examples.«system-verilog».comb_ops.comb_hint
