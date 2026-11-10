import Examples.«system-verilog».comb_lin.gen
import Examples.«system-verilog».comb_multi.gen
import LeanModels.Sv.Comb2
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombProcTactic
import LeanModels.Sv.CombLib
import LeanModels.Sv.PinAxioms

/-!
# The grouped route of `sv_structure` and `sv_equations` (WP-LIN), as a regression test

`sv_structure` and `sv_equations` ask the one-driver, rank and cover obligations of a design of four or more sites that is
not a flat netlist on the sites that write the same signal only: the lists are computed by the tactic, the lemmas
`disjObl_of_groups`, `rankObl'_of_groups`, `coverObl_of_groups` (`coverOblM_of_groups` for a body of several windows) are
applied, and the kernel checks the lists. If the listing fails for any reason the tactic falls back to the original
obligation, and the proof still goes through: only the DIAGNOSTIC tells. `set_option sv_comb.group_report true` makes each
obligation say how many sites, reads and writers its list holds; these messages are pinned here, so a change to a grouping
lemma (or to the tactic's way of applying it) that sends the tactic back to the original route fails this file.

* `lin_chain` (nine plain sites, two windows per vector): the one-driver pairs are the four pairs of windows of one
  vector, the rank and the cover list the writers of the seventeen reads (the reads of the inputs have none).
* `add_proc_m` (the cell as ONE `always_comb` body writing two windows, `comb_multi`): the cover obligation of a body of
  several windows (`CoverOblM`).

Default heartbeats, but for `pm_settled` (300000): the quotient atoms of the affine forms (`CombView.Aff.qs`, 2026-11-10)
put three more names in each of the tactics' normalization lists and one more summand in every affine value; measured
on that tree, this proof fails at the default 200000 and passes at 210000. Build:
`lake build Examples.«system-verilog».comb_lin.chain`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombLib LeanModels.Sv.CombEq
open Examples.«system-verilog».comb_lin.gen
open Examples.«system-verilog».comb_multi.gen

namespace Examples.«system-verilog».comb_lin.chain

/--
info: sv_comb group: DisjObl, 4 same-signal pairs of 9 sites
---
info: sv_comb group: RankObl', 17 reads with 14 writers of 9 sites
-/
#guard_msgs (whitespace := lax) in
set_option sv_comb.group_report true in
theorem lin_struct (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) (hRW : (W : Int) < 2147483648) (hRP : (P : Int) < 2147483648)
    (hRK : (W : Int) + P < 2147483648) :
    CombDesign (lin_chain.sem W P) ∧ Acyclic (lin_chain.sem W P) := by
  sv_structure (rank := rippleRank (fun p => p / 2) (fun _ _ _ => 0))
  all_goals (intros; omega)

/--
info: sv_comb group: CoverObl, 17 reads with 14 writers of 9 sites
-/
#guard_msgs (whitespace := lax) in
set_option sv_comb.group_report true in
theorem lin_settled (W P : Nat) (hW : 2 ≤ W) (hP : 2 ≤ P) (hRW : (W : Int) < 2147483648) (hRP : (P : Int) < 2147483648)
    (hRK : (W : Int) + P < 2147483648)
    (hc : CombDesign (lin_chain.sem W P))
    (ha : Acyclic (lin_chain.sem W P)) (st : SvState) (heqs : CombEqs (lin_chain.sem W P) st)
    (hsh : StateShape (lin_chain.sem W P) st) (x y : BitVec (W + P))
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y)) : True := by
  sv_equations
  · trivial
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)

/--
info: sv_comb group: CoverOblM, 9 reads with 8 writers of 4 sites
-/
#guard_msgs (whitespace := lax) in
set_option sv_comb.group_report true in
set_option maxHeartbeats 300000 in
theorem pm_settled (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483648)
    {d' : Design2} (_hl : (add_proc_m.sem N).lowerComb = some d')
    (_hc : CombDesign d') (_ha : Acyclic d') (st : SvState) (_heqs : CombEqs d' st) (_hsh : StateShape d' st)
    (x y : BitVec N) (ci : Bool)
    (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y))
    (hCi : SvState.lookup st "cin" = some (LVec.ofBitVec (BitVec.ofBool ci))) : True := by
  sv_equations
  · trivial
  all_goals first
    | (intros; omega)
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)
    | (refine inKnown_ofBitVec hB ?_; omega)
    | (refine inKnown_ofBitVec hCi ?_; omega)

#pin_axioms lin_struct lin_settled pm_settled

end Examples.«system-verilog».comb_lin.chain
