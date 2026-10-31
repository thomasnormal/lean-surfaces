import Examples.«system-verilog».flat_net.gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombEqTactic

/-!
# `sv_equations?` on a flat netlist (WP-P3b)

The netlist view of `flat_net.sv` with its stable names. The LAST assign of the file drives a bit of the
vector output `s`, so the knownness fact of the last site is a pair (`(∃ v, …) ∧ KnownBit …`) and the
right-nested conjunction of knownness facts has one conjunct more than there are sites; `sv_equations`
used to count conjuncts, find 11 for 10 sites and leave the whole view unnamed in `key` with a warning.
It now takes the sites as the first conjuncts of each spine, so every site gets `eq_<signal>_<k>` and
`known_<signal>_<k>`, `s[3]` included (`eq_s_4`). Pinned verbatim.

The design is FLAT (every site plain, no parameter), so `sv_equations` DECIDES `auto`, `inRange`, `width`,
`bitRead` and `cover` (closed statements about the site list; `CombEqPlain.lean`) and returns no goal for
them: the hint says so, and the only obligations left are the three `inputsKnown` premises. The second
example runs `sv_equations` itself and closes everything that is left with the input premises; there is no
`cover_k` to close.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».flat_net.gen

namespace Examples.«system-verilog».flat_net.comb_hint

/--
info: sv_equations: the netlist view and the obligations
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_c_plain_0 : st.boolAt "c" 0 = st.boolAt "cin" 0
  eq_s_plain_1 : st.boolAt "s" 0 = (st.boolAt "a" 0 ^^ st.boolAt "b" 0 ^^ st.boolAt "c" 0)
  eq_c_plain_2 : st.boolAt "c" (Int.toNat 1) =
  (st.boolAt "a" 0 && st.boolAt "b" 0 || st.boolAt "c" 0 && (st.boolAt "a" 0 ^^ st.boolAt "b" 0))
  eq_s_plain_3 : st.boolAt "s" (Int.toNat 1) =
  (st.boolAt "a" (Int.toNat 1) ^^ st.boolAt "b" (Int.toNat 1) ^^ st.boolAt "c" (Int.toNat 1))
  eq_c_plain_4 : st.boolAt "c" (Int.toNat 2) =
  (st.boolAt "a" (Int.toNat 1) && st.boolAt "b" (Int.toNat 1) ||
    st.boolAt "c" (Int.toNat 1) && (st.boolAt "a" (Int.toNat 1) ^^ st.boolAt "b" (Int.toNat 1)))
  eq_s_plain_5 : st.boolAt "s" (Int.toNat 2) =
  (st.boolAt "a" (Int.toNat 2) ^^ st.boolAt "b" (Int.toNat 2) ^^ st.boolAt "c" (Int.toNat 2))
  eq_c_plain_6 : st.boolAt "c" (Int.toNat 3) =
  (st.boolAt "a" (Int.toNat 2) && st.boolAt "b" (Int.toNat 2) ||
    st.boolAt "c" (Int.toNat 2) && (st.boolAt "a" (Int.toNat 2) ^^ st.boolAt "b" (Int.toNat 2)))
  eq_c_plain_7 : st.boolAt "c" (Int.toNat 4) =
  (st.boolAt "a" (Int.toNat 3) && st.boolAt "b" (Int.toNat 3) ||
    st.boolAt "c" (Int.toNat 3) && (st.boolAt "a" (Int.toNat 3) ^^ st.boolAt "b" (Int.toNat 3)))
  eq_cout_plain_8 : st.boolAt "cout" 0 = st.boolAt "c" (Int.toNat 4)
  eq_s_plain_9 : st.boolAt "s" (Int.toNat 3) =
  (st.boolAt "a" (Int.toNat 3) ^^ st.boolAt "b" (Int.toNat 3) ^^ st.boolAt "c" (Int.toNat 3))
  known_c_plain_0 : (∃ v, st.lookup "c" = some v ∧ v.width = Int.natAbs 4 + 1) ∧ KnownBit st "c" 0
  known_s_plain_1 : (∃ v, st.lookup "s" = some v ∧ v.width = Int.natAbs 3 + 1) ∧ KnownBit st "s" 0
  known_c_plain_2 : (∃ v, st.lookup "c" = some v ∧ v.width = Int.natAbs 4 + 1) ∧ KnownBit st "c" (Int.toNat 1)
  known_s_plain_3 : (∃ v, st.lookup "s" = some v ∧ v.width = Int.natAbs 3 + 1) ∧ KnownBit st "s" (Int.toNat 1)
  known_c_plain_4 : (∃ v, st.lookup "c" = some v ∧ v.width = Int.natAbs 4 + 1) ∧ KnownBit st "c" (Int.toNat 2)
  known_s_plain_5 : (∃ v, st.lookup "s" = some v ∧ v.width = Int.natAbs 3 + 1) ∧ KnownBit st "s" (Int.toNat 2)
  known_c_plain_6 : (∃ v, st.lookup "c" = some v ∧ v.width = Int.natAbs 4 + 1) ∧ KnownBit st "c" (Int.toNat 3)
  known_c_plain_7 : (∃ v, st.lookup "c" = some v ∧ v.width = Int.natAbs 4 + 1) ∧ KnownBit st "c" (Int.toNat 4)
  known_cout_plain_8 : (∃ v, st.lookup "cout" = some v ∧ v.width = 1) ∧ KnownBit st "cout" 0
  known_s_plain_9 : (∃ v, st.lookup "s" = some v ∧ v.width = Int.natAbs 3 + 1) ∧ KnownBit st "s" (Int.toNat 3)
  stable aliases (copies of the above; same statements):
    eq_c_1 := eq_c_plain_0    known_c_1 := known_c_plain_0
    eq_s_1 := eq_s_plain_1    known_s_1 := known_s_plain_1
    eq_c_2 := eq_c_plain_2    known_c_2 := known_c_plain_2
    eq_s_2 := eq_s_plain_3    known_s_2 := known_s_plain_3
    eq_c_3 := eq_c_plain_4    known_c_3 := known_c_plain_4
    eq_s_3 := eq_s_plain_5    known_s_3 := known_s_plain_5
    eq_c_4 := eq_c_plain_6    known_c_4 := known_c_plain_6
    eq_c_5 := eq_c_plain_7    known_c_5 := known_c_plain_7
    eq_cout_1 := eq_cout_plain_8    known_cout_1 := known_cout_plain_8
    eq_s_4 := eq_s_plain_9    known_s_4 := known_s_plain_9
  decided (flat netlist: every site plain, no parameter): auto, inRange, width, bitRead, cover
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = 4
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = 4
  [inputsKnown_3] ⊢ ∃ v, st.lookup "cin" = some v ∧ v.allKnown = true ∧ v.width = 1
-/
#guard_msgs (whitespace := lax) in
example :
    flat_net.sem ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec 4) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) → True := by
  have hc : CombDesign flat_net.sem := by sv_structure
  have ha : Acyclic flat_net.sem := by
    sv_structure (rank := rippleRank (fun p => [0, 1, 1, 2, 2, 3, 3, 4, 5, 4].getD p 0) (fun _ _ _ => 0))
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y ci hA hB hCi
  sv_equations?
  trivial

/-- `sv_equations` itself: the main goal, then ONLY the three `inputsKnown` premises (no `width`, `bitRead`
or `cover_k` goal); the aliases (`eq_s_4`, the last site) are in the context of the main goal. -/
example :
    flat_net.sem ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec 4) (ci : Bool),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) →
        SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci)) → True := by
  have hc : CombDesign flat_net.sem := by sv_structure
  have ha : Acyclic flat_net.sem := by
    sv_structure (rank := rippleRank (fun p => [0, 1, 1, 2, 2, 3, 3, 4, 5, 4].getD p 0) (fun _ _ _ => 0))
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y ci hA hB hCi
  sv_equations
  · have : eq_s_4 = eq_s_plain_9 := rfl
    have _ := known_s_4
    trivial
  · exact inKnown_ofBitVec hA (by omega)
  · exact inKnown_ofBitVec hB (by omega)
  · exact inKnown_ofBitVec hCi (by omega)

end Examples.«system-verilog».flat_net.comb_hint
