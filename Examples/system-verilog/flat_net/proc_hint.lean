import Examples.«system-verilog».flat_net.proc_gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombProcTactic

/-!
# `sv_equations?` on a flat design with an `always_comb` (WP-P3b)

The lowered design of `flat_proc.sv` (the `always_comb` replaced by the one assign it computes). The
`always_comb` is the LAST site and drives a bit of the vector output `y`, so the knownness fact of the
last site is a pair and the right-nested conjunction of knownness facts has one conjunct more than there
are sites. `sv_equations` used to count conjuncts and leave the whole view unnamed in `key` with a
warning; it now names every site (`eq_y_2`, the body's own `if`). Pinned verbatim.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».flat_net.proc_gen

namespace Examples.«system-verilog».flat_net.proc_hint

/--
info: sv_equations: the netlist view and the obligations (lowered design)
  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)
  eq_t_plain_0 : st.boolAt "t" 0 = (st.boolAt "a" 0 ^^ st.boolAt "b" 0)
  eq_y_plain_1 : st.boolAt "y" 0 = (st.boolAt "a" 0 && st.boolAt "c" 0)
  eq_y_plain_2 : st.boolAt "y" (Int.toNat 1) = if st.boolAt "c" 0 = true then st.boolAt "t" 0 else st.boolAt "a" 0 && st.boolAt "b" 0
  known_t_plain_0 : (∃ v, st.lookup "t" = some v ∧ v.width = 1) ∧ KnownBit st "t" 0
  known_y_plain_1 : (∃ v, st.lookup "y" = some v ∧ v.width = Int.natAbs 1 + 1) ∧ KnownBit st "y" 0
  known_y_plain_2 : (∃ v, st.lookup "y" = some v ∧ v.width = Int.natAbs 1 + 1) ∧ KnownBit st "y" (Int.toNat 1)
  stable aliases (copies of the above; same statements):
    eq_t_1 := eq_t_plain_0    known_t_1 := known_t_plain_0
    eq_y_1 := eq_y_plain_1    known_y_1 := known_y_plain_1
    eq_y_2 := eq_y_plain_2    known_y_2 := known_y_plain_2
  [inputsKnown_1] ⊢ ∃ v, st.lookup "a" = some v ∧ v.allKnown = true ∧ v.width = 1
  [inputsKnown_2] ⊢ ∃ v, st.lookup "b" = some v ∧ v.allKnown = true ∧ v.width = 1
  [inputsKnown_3] ⊢ ∃ v, st.lookup "c" = some v ∧ v.allKnown = true ∧ v.width = 1
-/
#guard_msgs (info, drop warning, whitespace := lax) in
example {d' : Design2} (hl : flat_proc.sem.lowerComb = some d')
    (hc : CombDesign d') (ha : Acyclic d') (st : SvState) (heqs : CombEqs d' st)
    (hsh : StateShape d' st) : True := by
  sv_equations?
  trivial

end Examples.«system-verilog».flat_net.proc_hint
