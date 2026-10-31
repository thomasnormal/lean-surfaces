import Lean
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombProcEq

/-!
# `sv_structure` / `sv_interface` / `sv_equations` for designs with `always_comb` bodies (WP-G, G2.2, R5)

The tactic names and syntax are those of `CombViewTactic.lean` / `CombEqTactic.lean`; this module adds a
SECOND elaborator to each syntax node, tried first. It handles exactly the goal shapes of the lowered design
and otherwise `throwUnsupportedSyntax`, so every existing proof elaborates unchanged (the regression
discipline of G2.2: the five reference proofs rebuild with this module imported).

| tactic | new goal shape | theorem applied |
|---|---|---|
| `sv_structure (rank := …)` / `(lexRank := …)` | `∃ d', (X.sem N).lowerComb = some d' ∧ CombDesign d' ∧ Acyclic d'` | `struct_viewL` / `struct_lex_viewL` |
| `sv_structure` | `∃ d', (X.sem N).lowerComb = some d' ∧ CombDesign d'` | `comb_viewL` |
| `sv_interface` | `t.Interface N (X.sem N)` with `hl : (X.sem N).lowerComb = some d'` in the context | `declsL_view` |
| `sv_equations` | `hl`, `hc : CombDesign d'`, `ha : Acyclic d'`, `heqs : CombEqs d' st`, `hsh : StateShape d' st` in the context | `eq_viewL` |

The recognizer is `PDesign.summaryP` (`CombProcSummary.lean`). A refused body is a tactic error whose first
line names the site (``sv_structure: outside the supported fragment — site `g_bit#1`: …``). The new
obligation is `noSelfRead_k` (`Summary.NoSelfRead`: no read window of a procedural body overlaps the window
it writes), closed by `intros; omega` like the index obligations; a body that reads the window it writes
VERBATIM is refused early by the tactic with the planned message, and a violation at a sampled small `N` is
reported with the offending site like the other obligations. `sv_cover` is unchanged.
-/

open Lean Elab Tactic Meta
open LeanModels.Sv.CombView

namespace LeanModels.Sv.CombView
namespace Summary

/-- The first sampled (site, valuation) where a procedural body reads a window that overlaps the window it
writes (a SAMPLE for the message only). -/
def selfReadCounterexample (s : Summary) (σ : String → Int) : Option String :=
  (s.instPairs σ).findSome? fun (ls, σ') =>
    if isCombProc ls.site.proc then
      ls.site.rds.findSome? fun r =>
        if (r.rd σ').overlaps (ls.site.tgt.win σ' (s.dw σ)) then
          some s!"`{ls.label (fun n => toString (σ' n))}` reads {r.showVal σ'}, which overlaps the window it writes ({showWin (ls.site.tgt.win σ' (s.dw σ))}): an `always_comb` body may not read what it writes"
        else none
    else none

/-- The early error: a procedural body reads, verbatim, the access it writes. -/
def selfReadSyntactic (s : Summary) : Option String :=
  s.lsites.findSome? fun ls =>
    if isCombProc ls.site.proc then
      ls.site.rds.findSome? fun r =>
        if decide (r = ls.site.tgt) then
          some s!"site `{ls.label id}`: always_comb reads the window it writes (`{ls.site.tgt.show}`)"
        else none
    else none

end Summary
end LeanModels.Sv.CombView

/-- `sv_norm_core` with the vocabulary of the procedural sites (`NoSelfRead`, the skeleton). -/
macro "svL_norm_core" : tactic =>
  `(tactic| (simp (config := { maxSteps := 4000000 }) only [LeanModels.Sv.CombProc.PTR.rds, LeanModels.Sv.CombView.Summary.NoSelfRead, LeanModels.Sv.CombView.isCombProc, LeanModels.Sv.CombView.Summary.EqsL, LeanModels.Sv.CombView.Summary.EqSiteL, LeanModels.Sv.CombView.Summary.WidthOblL, LeanModels.Sv.CombEq.rhsSk, LeanModels.Sv.CombEq.stmtSk, LeanModels.Sv.CombEq.stmtSkL, LeanModels.Sv.CombEq.stmtRcnt, LeanModels.Sv.CombEq.stmtRcntL, LeanModels.Sv.CombEq.rcnt, LeanModels.Sv.CombEq.pcnt, LeanModels.Sv.CombEq.PSk.bit, LeanModels.Sv.CombEq.PSk.WidthOk, LeanModels.Sv.CombView.Summary.AutoObl, LeanModels.Sv.CombView.Summary.lsites, LeanModels.Sv.CombView.Aff.add,
      LeanModels.Sv.CombView.Aff.var, LeanModels.Sv.CombView.Aff.const, List.append_nil,
      Int.zero_add, LeanModels.Sv.CombView.Aff.sub, LeanModels.Sv.CombView.Aff.neg,
      LeanModels.Sv.CombView.Aff.negTerms, Int.reduceNeg, Int.reduceAdd,
      List.nil_append, Nat.zero_add, Nat.reduceAdd,
      LeanModels.Sv.CombView.Aff.scale, LeanModels.Sv.CombView.Aff.scaleTerms, Int.mul_one,
      Int.mul_zero, List.map_cons, List.map_nil,
      List.cons_append, List.flatMap_cons, LeanModels.Sv.CombView.TFam.lsites,
      LeanModels.Sv.CombView.TFam.itemLs, LeanModels.Sv.CombView.Hdr.name, Option.getD_some,
      List.flatMap_nil, List.mem_cons, List.not_mem_nil,
      or_false, Int.ofNat_eq_natCast, List.zip_cons_cons,
      List.zip_nil_right, LeanModels.Sv.CombView.Summary.InR, LeanModels.Sv.CombView.Aff.eval,
      LeanModels.Sv.CombView.Summary.dm, LeanModels.Sv.CombView.Summary.find, LeanModels.Sv.CombView.findDecl,
      forall_eq_or_imp, LeanModels.Sv.CombView.Loops.all, forall_eq,
      LeanModels.Sv.CombView.Aff.evalTerms, Int.add_zero, Std.le_refl,
      String.reduceBEq, Bool.false_eq_true, not_false_eq_true,
      List.find?_cons_of_neg, BEq.rfl, List.find?_cons_of_pos,
      List.length_cons, List.length_nil, Nat.zero_lt_succ,
      getElem?_pos, List.getElem_cons_zero, LeanModels.Sv.CombView.σL,
      List.lookup_cons_self, Int.one_mul, true_and,
      false_implies, implies_true, Int.zero_le_ofNat,
      Nat.lt_add_one, List.getElem_cons_succ, and_true,
      LeanModels.Sv.CombView.Hdr.Rng, LeanModels.Sv.CombView.bindσ, String.reduceEq,
      ↓reduceIte, and_imp, Int.add_le_add_iff_right,
      Int.natCast_nonneg, and_self, LeanModels.Sv.CombView.Summary.DimNum,
      LeanModels.Sv.CombView.Summary.hdrPaths, Option.some.injEq, List.filterMap_cons_some,
      List.filterMap_nil, List.filterMap_cons_none, Int.natAbs_natCast,
      List.sum_cons, List.sum_nil, Nat.add_zero,
      Int.toNat_le, Int.natCast_add, Int.cast_ofNat_Int,
      Int.sub_zero, and_self_right, and_self_left,
      LeanModels.Sv.CombView.Summary.InRangeObl, LeanModels.Sv.CombView.Summary.InWin, LeanModels.Sv.CombView.Summary.dw,
      LeanModels.Sv.CombView.DeclT.width, Option.map_some, LeanModels.Sv.CombView.dimsW,
      Nat.mul_one, LeanModels.Sv.CombView.Summary.DisjObl, List.pairwise_cons,
      LeanModels.Sv.CombView.Summary.DisjOne, LeanModels.Sv.CombView.LSite.id, ne_eq,
      LeanModels.Sv.CombView.Acc.win, LeanModels.Sv.CombView.Acc.lo, LeanModels.Sv.CombView.Acc.wid,
      Int.toNat_natCast_add_one, LeanModels.Sv.CombView.SiteId.plain.injEq, Nat.zero_ne_one,
      LeanModels.Sv.Win.overlaps_eq_false, or_self, true_or,
      imp_self, reduceCtorEq, Int.toNat_natCast,
      not_true_eq_false, false_or, forall_const,
      Nat.reduceEqDiff, LeanModels.Sv.CombView.SiteId.fam.injEq, List.cons.injEq,
      List.cons_ne_self, and_false, false_and,
      List.ne_cons_self, Nat.succ_ne_self, List.Pairwise.nil,
      not_and, LeanModels.Sv.CombView.Summary.LexObl, LeanModels.Sv.CombView.Summary.RankObl',
      LeanModels.Sv.CombView.Summary.writersOf, LeanModels.Sv.CombView.Acc.name, List.mem_filter,
      beq_iff_eq, LeanModels.Sv.ReadWin.overlaps, LeanModels.Sv.CombView.Acc.rd,
      LeanModels.Sv.CombView.KLt, Nat.lt_irrefl, imp_false,
      Bool.not_eq_true, LeanModels.Sv.Win.overlaps_eq_true, Nat.lt_add_right_iff_pos,
      Nat.lt_add_left_iff_pos, Int.sub_add_cancel, Int.toNat_lt',
      Int.ofNat_toNat, LeanModels.Sv.CombView.Summary.RankObl, LeanModels.Sv.CombView.rippleRank,
      LeanModels.Sv.CombView.Summary.val, LeanModels.Sv.CombView.lpEnv, List.lookup_cons, List.lookup_nil,
      LeanModels.Sv.CombView.CE.eval]))

macro "svL_eq_norm_at" h:ident : tactic =>
  `(tactic| (simp (config := { maxSteps := 4000000 }) only [LeanModels.Sv.CombProc.PTR.rds, LeanModels.Sv.CombView.Summary.NoSelfRead, LeanModels.Sv.CombView.isCombProc, LeanModels.Sv.CombView.Summary.EqsL, LeanModels.Sv.CombView.Summary.EqSiteL, LeanModels.Sv.CombView.Summary.WidthOblL, LeanModels.Sv.CombEq.rhsSk, LeanModels.Sv.CombEq.stmtSk, LeanModels.Sv.CombEq.stmtSkL, LeanModels.Sv.CombEq.stmtRcnt, LeanModels.Sv.CombEq.stmtRcntL, LeanModels.Sv.CombEq.rcnt, LeanModels.Sv.CombEq.pcnt, LeanModels.Sv.CombEq.PSk.bit, LeanModels.Sv.CombEq.PSk.WidthOk, LeanModels.Sv.CombView.Summary.val, LeanModels.Sv.CombView.lpEnv, List.lookup_cons, List.lookup_nil, LeanModels.Sv.CombView.CE.eval,
      LeanModels.Sv.CombView.Summary.AutoObl, LeanModels.Sv.CombView.Summary.lsites, LeanModels.Sv.CombView.Aff.add,
      LeanModels.Sv.CombView.Aff.var, LeanModels.Sv.CombView.Aff.const, List.append_nil,
      Int.zero_add, LeanModels.Sv.CombView.Aff.sub, LeanModels.Sv.CombView.Aff.neg,
      LeanModels.Sv.CombView.Aff.negTerms, Int.reduceNeg, Int.reduceAdd,
      List.nil_append, Nat.zero_add, Nat.reduceAdd,
      LeanModels.Sv.CombView.Aff.scale, LeanModels.Sv.CombView.Aff.scaleTerms, Int.mul_one,
      Int.mul_zero, List.map_cons, List.map_nil,
      List.cons_append, List.flatMap_cons, LeanModels.Sv.CombView.TFam.lsites,
      LeanModels.Sv.CombView.TFam.itemLs, LeanModels.Sv.CombView.Hdr.name, Option.getD_some,
      List.flatMap_nil, List.mem_cons, List.not_mem_nil,
      or_false, Int.ofNat_eq_natCast, List.zip_cons_cons,
      List.zip_nil_right, LeanModels.Sv.CombView.Summary.InR, LeanModels.Sv.CombView.Aff.eval,
      LeanModels.Sv.CombView.Summary.dm, LeanModels.Sv.CombView.Summary.find, LeanModels.Sv.CombView.findDecl,
      forall_eq_or_imp, LeanModels.Sv.CombView.Loops.all, forall_eq,
      LeanModels.Sv.CombView.Aff.evalTerms, Int.add_zero, Std.le_refl,
      String.reduceBEq, Bool.false_eq_true, not_false_eq_true,
      List.find?_cons_of_neg, BEq.rfl, List.find?_cons_of_pos,
      List.length_cons, List.length_nil, Nat.zero_lt_succ,
      getElem?_pos, List.getElem_cons_zero, LeanModels.Sv.CombView.σL,
      List.lookup_cons_self, Int.one_mul, true_and,
      false_implies, implies_true, Int.zero_le_ofNat,
      Nat.lt_add_one, List.getElem_cons_succ, and_true,
      LeanModels.Sv.CombView.Hdr.Rng, LeanModels.Sv.CombView.bindσ, String.reduceEq,
      ↓reduceIte, and_imp, Int.add_le_add_iff_right,
      Int.natCast_nonneg, and_self, LeanModels.Sv.CombView.Summary.DimNum,
      LeanModels.Sv.CombView.Summary.hdrPaths, Option.some.injEq, List.filterMap_cons_some,
      List.filterMap_nil, List.filterMap_cons_none, Int.natAbs_natCast,
      List.sum_cons, List.sum_nil, Nat.add_zero,
      Int.toNat_le, Int.natCast_add, Int.cast_ofNat_Int,
      Int.sub_zero, and_self_right, and_self_left,
      LeanModels.Sv.CombView.Summary.InRangeObl, LeanModels.Sv.CombView.Summary.InWin, LeanModels.Sv.CombView.Summary.dw,
      LeanModels.Sv.CombView.DeclT.width, Option.map_some, LeanModels.Sv.CombView.dimsW,
      Nat.mul_one, LeanModels.Sv.CombView.Summary.DisjObl, List.pairwise_cons,
      LeanModels.Sv.CombView.Summary.DisjOne, LeanModels.Sv.CombView.LSite.id, ne_eq,
      LeanModels.Sv.CombView.Acc.win, LeanModels.Sv.CombView.Acc.lo, LeanModels.Sv.CombView.Acc.wid,
      Int.toNat_natCast_add_one, LeanModels.Sv.CombView.SiteId.plain.injEq, Nat.zero_ne_one,
      LeanModels.Sv.Win.overlaps_eq_false, or_self, true_or,
      imp_self, reduceCtorEq, Int.toNat_natCast,
      not_true_eq_false, false_or, forall_const,
      Nat.reduceEqDiff, LeanModels.Sv.CombView.SiteId.fam.injEq, List.cons.injEq,
      List.cons_ne_self, and_false, false_and,
      List.ne_cons_self, Nat.succ_ne_self, List.Pairwise.nil,
      not_and, LeanModels.Sv.CombView.Summary.LexObl, LeanModels.Sv.CombView.Summary.RankObl',
      LeanModels.Sv.CombView.Summary.writersOf, LeanModels.Sv.CombView.Acc.name, List.mem_filter,
      beq_iff_eq, LeanModels.Sv.ReadWin.overlaps, LeanModels.Sv.CombView.Acc.rd,
      LeanModels.Sv.CombView.KLt, Nat.lt_irrefl, imp_false,
      Bool.not_eq_true, LeanModels.Sv.Win.overlaps_eq_true, Nat.lt_add_right_iff_pos,
      Nat.lt_add_left_iff_pos, Int.sub_add_cancel, Int.toNat_lt',
      Int.ofNat_toNat, LeanModels.Sv.CombView.Summary.RankObl, LeanModels.Sv.CombView.rippleRank,
      LeanModels.Sv.CombView.Summary.Eqs, LeanModels.Sv.CombView.Summary.Knowns,
      LeanModels.Sv.CombView.Summary.EqSite, LeanModels.Sv.CombView.Summary.KnownSite,
      LeanModels.Sv.CombView.Summary.InKnown, LeanModels.Sv.CombView.Summary.inputNames,
      LeanModels.Sv.CombEq.LoopsN, LeanModels.Sv.CombEq.rhsOf, LeanModels.Sv.CombEq.skRhs,
      LeanModels.Sv.CombEq.skT, LeanModels.Sv.CombEq.partsT, LeanModels.Sv.CombEq.cnt,
      LeanModels.Sv.CombEq.mkGate, LeanModels.Sv.CombEq.Sk.bit, LeanModels.Sv.CombEq.accBit,
      LeanModels.Sv.CombEq.catBit, LeanModels.Sv.CombEq.Part.bit, LeanModels.Sv.CombEq.Part.wid,
      LeanModels.Sv.CombView.gateOf, Int.ofNat_lt, Int.ofNat_le, List.take_nil, List.drop_nil,
      List.take_succ_cons, List.drop_succ_cons, List.take_zero, List.drop_zero, List.headD_cons,
      List.headD_nil, Nat.lt_one_iff, Nat.add_zero, Int.toNat_zero, Nat.zero_add,
      LeanModels.Sv.CombEq.rmN_zero_zero_add, LeanModels.Sv.CombEq.rmN_zero_row,
      LeanModels.Sv.CombEq.logic_l0_beq_l1, LeanModels.Sv.CombEq.logic_l1_beq_l1,
      LeanModels.Sv.CombEq.lvec_boolAt_l0, LeanModels.Sv.CombEq.lvec_boolAt_l1_zero,
      LeanModels.Sv.CombEq.lvec_width_l0, Nat.not_lt_zero, Nat.sub_zero, Nat.add_sub_cancel, Nat.zero_lt_succ, List.sum_cons, List.sum_nil, List.map_cons, List.map_nil,
      LeanModels.Sv.CombView.Summary.WidthObl, LeanModels.Sv.CombView.Summary.BitReadObl,
      LeanModels.Sv.CombView.Summary.CoverObl, LeanModels.Sv.CombView.Summary.SrcS,
      LeanModels.Sv.CombEq.LoopsE, LeanModels.Sv.CombEq.accBitUpper, LeanModels.Sv.CombEq.Sk.WidthOk,
      LeanModels.Sv.CombEq.Part.wid, LeanModels.Sv.CombEq.Part.bit] at $h:ident; sv_lp_norm_at $h))

macro "svL_eq_norm" : tactic =>
  `(tactic| (simp (config := { maxSteps := 4000000 }) only [LeanModels.Sv.CombProc.PTR.rds, LeanModels.Sv.CombView.Summary.NoSelfRead, LeanModels.Sv.CombView.isCombProc, LeanModels.Sv.CombView.Summary.EqsL, LeanModels.Sv.CombView.Summary.EqSiteL, LeanModels.Sv.CombView.Summary.WidthOblL, LeanModels.Sv.CombEq.rhsSk, LeanModels.Sv.CombEq.stmtSk, LeanModels.Sv.CombEq.stmtSkL, LeanModels.Sv.CombEq.stmtRcnt, LeanModels.Sv.CombEq.stmtRcntL, LeanModels.Sv.CombEq.rcnt, LeanModels.Sv.CombEq.pcnt, LeanModels.Sv.CombEq.PSk.bit, LeanModels.Sv.CombEq.PSk.WidthOk, LeanModels.Sv.CombView.Summary.val, LeanModels.Sv.CombView.lpEnv, List.lookup_cons, List.lookup_nil, LeanModels.Sv.CombView.CE.eval,
      LeanModels.Sv.CombView.Summary.AutoObl, LeanModels.Sv.CombView.Summary.lsites, LeanModels.Sv.CombView.Aff.add,
      LeanModels.Sv.CombView.Aff.var, LeanModels.Sv.CombView.Aff.const, List.append_nil,
      Int.zero_add, LeanModels.Sv.CombView.Aff.sub, LeanModels.Sv.CombView.Aff.neg,
      LeanModels.Sv.CombView.Aff.negTerms, Int.reduceNeg, Int.reduceAdd,
      List.nil_append, Nat.zero_add, Nat.reduceAdd,
      LeanModels.Sv.CombView.Aff.scale, LeanModels.Sv.CombView.Aff.scaleTerms, Int.mul_one,
      Int.mul_zero, List.map_cons, List.map_nil,
      List.cons_append, List.flatMap_cons, LeanModels.Sv.CombView.TFam.lsites,
      LeanModels.Sv.CombView.TFam.itemLs, LeanModels.Sv.CombView.Hdr.name, Option.getD_some,
      List.flatMap_nil, List.mem_cons, List.not_mem_nil,
      or_false, Int.ofNat_eq_natCast, List.zip_cons_cons,
      List.zip_nil_right, LeanModels.Sv.CombView.Summary.InR, LeanModels.Sv.CombView.Aff.eval,
      LeanModels.Sv.CombView.Summary.dm, LeanModels.Sv.CombView.Summary.find, LeanModels.Sv.CombView.findDecl,
      forall_eq_or_imp, LeanModels.Sv.CombView.Loops.all, forall_eq,
      LeanModels.Sv.CombView.Aff.evalTerms, Int.add_zero, Std.le_refl,
      String.reduceBEq, Bool.false_eq_true, not_false_eq_true,
      List.find?_cons_of_neg, BEq.rfl, List.find?_cons_of_pos,
      List.length_cons, List.length_nil, Nat.zero_lt_succ,
      getElem?_pos, List.getElem_cons_zero, LeanModels.Sv.CombView.σL,
      List.lookup_cons_self, Int.one_mul, true_and,
      false_implies, implies_true, Int.zero_le_ofNat,
      Nat.lt_add_one, List.getElem_cons_succ, and_true,
      LeanModels.Sv.CombView.Hdr.Rng, LeanModels.Sv.CombView.bindσ, String.reduceEq,
      ↓reduceIte, and_imp, Int.add_le_add_iff_right,
      Int.natCast_nonneg, and_self, LeanModels.Sv.CombView.Summary.DimNum,
      LeanModels.Sv.CombView.Summary.hdrPaths, Option.some.injEq, List.filterMap_cons_some,
      List.filterMap_nil, List.filterMap_cons_none, Int.natAbs_natCast,
      List.sum_cons, List.sum_nil, Nat.add_zero,
      Int.toNat_le, Int.natCast_add, Int.cast_ofNat_Int,
      Int.sub_zero, and_self_right, and_self_left,
      LeanModels.Sv.CombView.Summary.InRangeObl, LeanModels.Sv.CombView.Summary.InWin, LeanModels.Sv.CombView.Summary.dw,
      LeanModels.Sv.CombView.DeclT.width, Option.map_some, LeanModels.Sv.CombView.dimsW,
      Nat.mul_one, LeanModels.Sv.CombView.Summary.DisjObl, List.pairwise_cons,
      LeanModels.Sv.CombView.Summary.DisjOne, LeanModels.Sv.CombView.LSite.id, ne_eq,
      LeanModels.Sv.CombView.Acc.win, LeanModels.Sv.CombView.Acc.lo, LeanModels.Sv.CombView.Acc.wid,
      Int.toNat_natCast_add_one, LeanModels.Sv.CombView.SiteId.plain.injEq, Nat.zero_ne_one,
      LeanModels.Sv.Win.overlaps_eq_false, or_self, true_or,
      imp_self, reduceCtorEq, Int.toNat_natCast,
      not_true_eq_false, false_or, forall_const,
      Nat.reduceEqDiff, LeanModels.Sv.CombView.SiteId.fam.injEq, List.cons.injEq,
      List.cons_ne_self, and_false, false_and,
      List.ne_cons_self, Nat.succ_ne_self, List.Pairwise.nil,
      not_and, LeanModels.Sv.CombView.Summary.LexObl, LeanModels.Sv.CombView.Summary.RankObl',
      LeanModels.Sv.CombView.Summary.writersOf, LeanModels.Sv.CombView.Acc.name, List.mem_filter,
      beq_iff_eq, LeanModels.Sv.ReadWin.overlaps, LeanModels.Sv.CombView.Acc.rd,
      LeanModels.Sv.CombView.KLt, Nat.lt_irrefl, imp_false,
      Bool.not_eq_true, LeanModels.Sv.Win.overlaps_eq_true, Nat.lt_add_right_iff_pos,
      Nat.lt_add_left_iff_pos, Int.sub_add_cancel, Int.toNat_lt',
      Int.ofNat_toNat, LeanModels.Sv.CombView.Summary.RankObl, LeanModels.Sv.CombView.rippleRank,
      LeanModels.Sv.CombView.Summary.Eqs, LeanModels.Sv.CombView.Summary.Knowns,
      LeanModels.Sv.CombView.Summary.EqSite, LeanModels.Sv.CombView.Summary.KnownSite,
      LeanModels.Sv.CombView.Summary.InKnown, LeanModels.Sv.CombView.Summary.inputNames,
      LeanModels.Sv.CombEq.LoopsN, LeanModels.Sv.CombEq.rhsOf, LeanModels.Sv.CombEq.skRhs,
      LeanModels.Sv.CombEq.skT, LeanModels.Sv.CombEq.partsT, LeanModels.Sv.CombEq.cnt,
      LeanModels.Sv.CombEq.mkGate, LeanModels.Sv.CombEq.Sk.bit, LeanModels.Sv.CombEq.accBit,
      LeanModels.Sv.CombEq.catBit, LeanModels.Sv.CombEq.Part.bit, LeanModels.Sv.CombEq.Part.wid,
      LeanModels.Sv.CombView.gateOf, Int.ofNat_lt, Int.ofNat_le, List.take_nil, List.drop_nil,
      List.take_succ_cons, List.drop_succ_cons, List.take_zero, List.drop_zero, List.headD_cons,
      List.headD_nil, Nat.lt_one_iff, Nat.add_zero, Int.toNat_zero, Nat.zero_add,
      LeanModels.Sv.CombEq.logic_l0_beq_l1, LeanModels.Sv.CombEq.logic_l1_beq_l1,
      LeanModels.Sv.CombEq.lvec_boolAt_l0, LeanModels.Sv.CombEq.lvec_boolAt_l1_zero,
      LeanModels.Sv.CombEq.lvec_width_l0, Nat.not_lt_zero, Nat.sub_zero, Nat.add_sub_cancel, Nat.zero_lt_succ, List.sum_cons, List.sum_nil, List.map_cons, List.map_nil,
      LeanModels.Sv.CombView.Summary.WidthObl, LeanModels.Sv.CombView.Summary.BitReadObl,
      LeanModels.Sv.CombView.Summary.CoverObl, LeanModels.Sv.CombView.Summary.SrcS,
      LeanModels.Sv.CombEq.LoopsE, LeanModels.Sv.CombEq.accBitUpper, LeanModels.Sv.CombEq.Sk.WidthOk,
      LeanModels.Sv.CombEq.Part.wid, LeanModels.Sv.CombEq.Part.bit]; sv_lp_norm))

/-- `svL_norm [f, g]`: the normalization, with the player's own rank/key definitions `f`, `g` unfolded. -/
syntax "svL_norm" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| svL_norm) => `(tactic| (svL_norm_core; sv_lp_norm; try simp))
  | `(tactic| svL_norm [$ids,*]) =>
      `(tactic| (svL_norm_core; sv_lp_norm; (try simp (config := { maxSteps := 4000000 }) only [$ids,*]); try simp))


/-- **Run one of the new elaborators.** The framework tries the elaborators registered for a syntax node
latest first and, when one FAILS (an error, or an abort), restores the state and tries the next, reporting the
failure of the LAST one tried: the original elaborator's generic "the goal must be …". A new elaborator that
has recognised its goal shape must not fall through, so its error is logged here and the goal is admitted
(Lean's own error recovery for a tactic block: the message is the one the user sees, and `#guard_msgs` pins
it); `unsupportedSyntax`, thrown before anything is decided, still falls through to the original. -/
private def guardL (act : TacticM Unit) : TacticM Unit := do
  try act
  catch ex =>
    match ex with
    | .internal _ _ => throw ex
    | _ =>
        logException ex
        for g in ← getGoals do
          unless ← g.isAssigned do g.admit
        setGoals []

unsafe def evalSummaryP (pd : Expr) : MetaM (Except String Summary) := do
  let ty := mkApp2 (mkConst ``Except [Level.zero, Level.zero]) (mkConst ``String)
    (mkConst ``LeanModels.Sv.CombView.Summary)
  evalExpr (Except String Summary) ty (mkApp (mkConst ``LeanModels.Sv.PDesign.summaryP) pd)

/-- `X.sem N` is `PDesign.instantiateGD2 X.pdesign [↑N]`: unfold until it shows. -/
private partial def findGD2L (e : Expr) (fuel : Nat) : MetaM (Option (Expr × Expr)) := do
  let e ← whnfCore e
  if e.isAppOfArity ``LeanModels.Sv.PDesign.instantiateGD2 2 then
    return some (e.getAppArgs[0]!, e.getAppArgs[1]!)
  match fuel with
  | 0 => return none
  | fuel + 1 =>
    match ← unfoldDefinition? e with
    | some e' => findGD2L e' fuel
    | none => return none

private partial def fvarsOfL (e : Expr) : Array FVarId := Id.run do
  let mut acc : Array FVarId := #[]
  repeat
    match e.find? (fun x => x.isFVar && !acc.contains x.fvarId!) with
    | some x => acc := acc.push x.fvarId!
    | none => break
  return acc

private def lowerBoundsL (fvs : Array FVarId) : MetaM Nat := do
  let mut lb := 1
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    let check (small big : Expr) (strict : Bool) : MetaM Nat := do
      if big.isFVar && fvs.contains big.fvarId! then
        match ← Meta.evalNat small with
        | some c => return (if strict then c + 1 else c)
        | none => return 0
      else return 0
    if t.isAppOfArity ``LE.le 4 then
      lb := max lb (← check t.getAppArgs[2]! t.getAppArgs[3]! false)
    else if t.isAppOfArity ``LT.lt 4 then
      lb := max lb (← check t.getAppArgs[2]! t.getAppArgs[3]! true)
    else if t.isAppOfArity ``GE.ge 4 then
      lb := max lb (← check t.getAppArgs[3]! t.getAppArgs[2]! false)
    else if t.isAppOfArity ``GT.gt 4 then
      lb := max lb (← check t.getAppArgs[3]! t.getAppArgs[2]! true)
  return lb

private def headConstL? (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const n _ => some n
  | _ => none

/-- The hypothesis `hl : (X.sem N).lowerComb = some d'`: its name and `X.sem N`. -/
private def findLowerHyp : MetaM (Option (Name × Expr)) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if t.isAppOfArity ``Eq 3 && (t.getArg! 1).isAppOfArity ``LeanModels.Sv.Design2.lowerComb 1 then
      return some (d.userName, (t.getArg! 1).appArg!)
  return none

/-! ## `sv_structure` -/

unsafe def runSvStructureL (rankStx? lexStx? : Option Syntax) (hintOnly : Bool) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    unless ty.isAppOfArity ``Exists 2 do throwUnsupportedSyntax
    let some lc := ty.find? (fun e => e.isAppOfArity ``LeanModels.Sv.Design2.lowerComb 1)
      | throwUnsupportedSyntax
    let hasComb := (ty.find? (fun e => e.isConstOf ``LeanModels.Sv.CombDesign)).isSome
    let isAcyc := (ty.find? (fun e => e.isConstOf ``LeanModels.Sv.Acyclic)).isSome
    unless hasComb do throwUnsupportedSyntax
    let some (pd, args) ← findGD2L lc.appArg! 8
      | throwError "sv_structure: cannot read a `load_design_sv2` family (`X.sem N`) off the design in the goal"
    let some pdName := headConstL? pd
      | throwError "sv_structure: the design is not a named constant"
    match ← evalSummaryP pd with
    | .error msg =>
        throwError "sv_structure: outside the supported fragment — {msg}"
    | .ok s =>
      if hintOnly then
        logInfo m!"{s.describe}"
        return
      let probs := s.structProblems
      unless probs.isEmpty do
        throwError "sv_structure: structural check failed:\n  {"\n  ".intercalate probs}"
      if let some m := s.selfReadSyntactic then
        throwError "sv_structure: outside the supported fragment — {m}"
      let fvs ← (fvarsOfL args).filterM fun f => do
        return (← f.getType).isConstOf ``Nat
      let lb ← lowerBoundsL fvs
      let rankE? : Option Expr ← match rankStx? with
        | none => pure none
        | some stx => do
            let rty := Lean.mkForall `x BinderInfo.default (mkConst ``LeanModels.Sv.CombView.SiteId)
              (mkConst ``Nat)
            some <$> Tactic.elabTermEnsuringType stx rty
      let lexE? : Option Expr ← match lexStx? with
        | none => pure none
        | some stx => do
            let rty := Lean.mkForall `x BinderInfo.default (mkConst ``LeanModels.Sv.CombView.SiteId)
              (mkConst ``LeanModels.Sv.CombView.Key)
            some <$> Tactic.elabTermEnsuringType stx rty
      if isAcyc && rankE?.isNone && lexE?.isNone then
        throwError "sv_structure: an `Acyclic` goal needs a rank over site identities, e.g. `sv_structure (rank := rippleRank … …)` or a lexicographic key `sv_structure (lexRank := fun | .plain 0 => (0, 0, 0) | …)`; run `sv_structure?` to see the sites and the rank relation they must satisfy"
      for k in [lb, lb + 1, lb + 2, lb + 4] do
        let lits := fvs.map fun _ => (mkNatLit k)
        let argsK := args.replaceFVars (fvs.map mkFVar) lits
        let argVals ← evalArgs argsK
        let σ := s.val argVals
        let ctxMsg := s!"(sampled at {s.pnames} = {argVals}; a genuine violation, not a missing proof, unless your hypotheses exclude this point)"
        if let some m := s.accCounterexample σ then
          throwError "sv_structure: in-range obligation fails — {m} {ctxMsg}"
        if let some m := s.rangeCounterexample σ then
          throwError "sv_structure: in-range obligation fails — {m} {ctxMsg}"
        if let some m := s.selfReadCounterexample σ then
          throwError "sv_structure: noSelfRead obligation fails — {m} {ctxMsg}"
        if let some m := s.disjCounterexample σ then
          throwError "sv_structure: {m} {ctxMsg}"
        if let some re := rankE? then
          let reK := re.replaceFVars (fvs.map mkFVar) lits
          let ρ ← evalRank reK
          if let some m := s.rankCounterexample σ (fun w r => decide (ρ w < ρ r))
              (fun i => toString (ρ i)) then
            throwError "sv_structure: {m} {ctxMsg}"
        if let some le := lexE? then
          let leK := le.replaceFVars (fvs.map mkFVar) lits
          let κ ← evalLex leK
          if let some m := s.rankCounterexample σ (fun w r => decide (KLt (κ w) (κ r)))
              (fun i => showKey (κ i)) then
            throwError "sv_structure: {m} {ctxMsg}"
      let pdId := mkIdent pdName
      let keyIds : Array Ident :=
        match (rankE?.orElse fun _ => lexE?) with
        | some e =>
            match e.getAppFn with
            | .const n _ => #[mkIdent n]
            | _ => #[]
        | none => #[]
      let keyLemmas ← keyIds.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
      if !isAcyc then
        evalTactic (← `(tactic|
          refine LeanModels.Sv.CombView.comb_viewL (s := ?s) (env := ?env) (hs := ?hs) (harity := ?harity)
            (h1 := ?h1) (hag := ?hag) (hok := ?hok) (hauto := ?hauto) (hin := ?hin) (hdisj := ?hdisj)
            (hself := ?hself)))
      else if lexE?.isSome then
        let r ← match lexStx? with
          | some r => pure r
          | none => throwError "unreachable"
        let rT : TSyntax `term := ⟨r⟩
        evalTactic (← `(tactic|
          refine LeanModels.Sv.CombView.struct_lex_viewL (s := ?s) (env := ?env) (hs := ?hs)
            (harity := ?harity) (h1 := ?h1) (hag := ?hag) (hok := ?hok) (hauto := ?hauto) (hin := ?hin)
            (hdisj := ?hdisj) (hself := ?hself) (κ := $rT) (hrank := ?hrank)))
      else
        let r ← match rankStx? with
          | some r => pure r
          | none => throwError "unreachable"
        let rT : TSyntax `term := ⟨r⟩
        evalTactic (← `(tactic|
          refine LeanModels.Sv.CombView.struct_viewL (s := ?s) (env := ?env) (hs := ?hs)
            (harity := ?harity) (h1 := ?h1) (hag := ?hag) (hok := ?hok) (hauto := ?hauto) (hin := ?hin)
            (hdisj := ?hdisj) (hself := ?hself) (ρ := $rT) (hrank := ?hrank)))
      let goals ← getGoals
      let find (n : Name) : TacticM MVarId := do
        for g in goals do
          if (← g.getTag).eraseMacroScopes == n then return g
        throwError "sv_structure: internal error: goal `{n}` not found"
      let closeWith (n : Name) (what : String) (tac : TSyntax `tactic) : TacticM Unit := do
        setGoals [← find n]
        try
          evalTactic tac
        catch e =>
          throwError "sv_structure: {what}\n{e.toMessageData}"
        unless (← getGoals).isEmpty do
          throwError "sv_structure: {what}"
      let closeDecide (n : Name) (what : String) : TacticM Unit := do
        setGoals [← find n]
        try
          closeByDecide (← getMainGoal) what
          setGoals []
        catch _ =>
          closeWith n what (← `(tactic| decide +kernel))
      closeWith `hs "the recognizer's summary could not be computed by `rfl`" (← `(tactic| rfl))
      closeWith `harity "the number of arguments differs from the number of parameters" (← `(tactic| rfl))
      closeWith `h1 "the parameter stage (`paramEnv2`) of this design could not be evaluated at a symbolic parameter" (← `(tactic| rfl))
      closeWith `hag "the parameter values could not be read off the instantiation environment" (← `(tactic| rfl))
      closeDecide `hok "the structural check failed"
      let mut out : Array MVarId := #[]
      let runOb (n : Name) (nm : String) (tac : TSyntax ``Lean.Parser.Tactic.tacticSeq) :
          TacticM (List MVarId) := do
        setGoals [← find n]
        evalTactic tac
        let rest ← getGoals
        let k := rest.length
        let mut i := 0
        for g in rest do
          i := i + 1
          g.setTag (if k == 1 then Name.mkSimple nm else Name.mkSimple s!"{nm}_{i}")
        return rest
      out := out ++ (← runOb `hauto "auto" (← `(tacticSeq|
        (try simp only [$pdId:ident])
        svL_norm [$keyLemmas,*]
        repeat' refine And.intro ?_ ?_
        all_goals first | (intros; omega) | skip))).toArray
      out := out ++ (← runOb `hin "inRange" (← `(tacticSeq|
        (try simp only [$pdId:ident])
        svL_norm [$keyLemmas,*]
        repeat' refine And.intro ?_ ?_))).toArray
      out := out ++ (← runOb `hself "noSelfRead" (← `(tacticSeq|
        (try simp only [$pdId:ident])
        svL_norm [$keyLemmas,*]
        repeat' refine And.intro ?_ ?_))).toArray
      out := out ++ (← runOb `hdisj "driverDisjoint" (← `(tacticSeq|
        (try simp only [$pdId:ident])
        svL_norm [$keyLemmas,*]
        repeat' refine And.intro ?_ ?_))).toArray
      if isAcyc then
        out := out ++ (← runOb `hrank "rankDecreases" (← `(tacticSeq|
          (try simp only [$pdId:ident])
          svL_norm [$keyLemmas,*]
          repeat' refine And.intro ?_ ?_))).toArray
      setGoals out.toList

@[tactic svStructure] unsafe def evalSvStructureL : Tactic := fun stx => guardL do
  unless stx[2].isNone do throwUnsupportedSyntax
  if stx[1].isNone then
    withDeepRec (runSvStructureL none none false)
  else
    let cl := stx[1][0]
    if cl[1].getAtomVal == "lexRank" then withDeepRec (runSvStructureL none (some cl[3]) false)
    else withDeepRec (runSvStructureL (some cl[3]) none false)

@[tactic svStructureQ] unsafe def evalSvStructureQL : Tactic := fun _ => guardL do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    unless ty.isAppOfArity ``Exists 2 do throwUnsupportedSyntax
  withDeepRec (runSvStructureL none none true)

/-! ## `sv_interface` -/

unsafe def runSvInterfaceL : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    unless ty.isApp && ty.getAppNumArgs ≥ 3 && ty.getAppFn.isConst do throwUnsupportedSyntax
    let D := ty.appArg!
    let some (hlN, X) ← findLowerHyp | throwUnsupportedSyntax
    unless ← isDefEq X D do throwUnsupportedSyntax
    let some (pd, args) ← findGD2L D 8
      | throwError "sv_interface: cannot read a `load_design_sv2` family (`X.sem N`) off the design in the goal"
    let some pdName := headConstL? pd
      | throwError "sv_interface: the design is not a named constant"
    match ← evalSummaryP pd with
    | .error msg => throwError "sv_interface: outside the supported fragment — {msg}"
    | .ok s =>
      let probs := s.structProblems
      unless probs.isEmpty do
        throwError "sv_interface: structural check failed:\n  {"\n  ".intercalate probs}"
      let pdId := mkIdent pdName
      let hlI := mkIdent hlN
      let keyI := mkIdent `key
      let D' := mkApp2 (mkConst ``LeanModels.Sv.PDesign.instantiateGD2) pd args
      let ty' := ty.replace fun e => if e == D then some D' else none
      replaceMainGoal [← goal.replaceTargetDefEq ty']
      evalTactic (← `(tactic|
        have $keyI:ident := LeanModels.Sv.CombEq.declsL_view (s := ?s) (env := ?env) (hs := ?hs)
            (h1 := ?h1) (hag := ?hag) (hok := ?hok) (hl := $hlI)))
      let goals ← getGoals
      let named : List Name := [`s, `env, `hs, `h1, `hag, `hok]
      let mut bodyGoal? : Option MVarId := none
      for g in goals do
        unless named.contains (← g.getTag).eraseMacroScopes do
          if bodyGoal?.isNone then bodyGoal? := some g
      let some bodyGoal := bodyGoal?
        | throwError "sv_interface: internal error: no main goal after introducing the declarations"
      let find (n : Name) : TacticM MVarId := do
        for g in goals do
          if (← g.getTag).eraseMacroScopes == n then return g
        throwError "sv_interface: internal error: goal `{n}` not found"
      let closeWith (n : Name) (what : String) (tac : TSyntax `tactic) : TacticM Unit := do
        setGoals [← find n]
        try
          evalTactic tac
        catch e =>
          throwError "sv_interface: {what}\n{e.toMessageData}"
        unless (← getGoals).isEmpty do
          throwError "sv_interface: {what}"
      let closeDecide (n : Name) (what : String) : TacticM Unit := do
        setGoals [← find n]
        try
          closeByDecide (← getMainGoal) what
          setGoals []
        catch _ =>
          closeWith n what (← `(tactic| decide +kernel))
      closeWith `hs "the recognizer's summary could not be computed by `rfl`" (← `(tactic| rfl))
      closeWith `h1 "the parameter stage (`paramEnv2`) of this design could not be evaluated at a symbolic parameter" (← `(tactic| rfl))
      closeWith `hag "the parameter values could not be read off the instantiation environment" (← `(tactic| rfl))
      closeDecide `hok "the structural check failed"
      setGoals [bodyGoal]
      let headId := mkIdent ty.getAppFn.constName!
      let taskIds : Array Ident :=
        match ty.getArg! 0 with
        | .const n _ => #[mkIdent n]
        | _ => #[]
      let taskLemmas ← taskIds.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
      try
        let inPorts := mkIdent `SvGolf.inputPorts
        let outPorts := mkIdent `SvGolf.outputPorts
        evalTactic (← `(tactic| simp only [$headId:ident, $inPorts:ident, $outPorts:ident]))
        evalTactic (← `(tactic| rw [$keyI:ident]))
        evalTactic (← `(tactic|
          simp [LeanModels.Sv.CombView.DeclT.toDecl, LeanModels.Sv.CombView.DeclT.width,
            LeanModels.Sv.CombView.dimsW, LeanModels.Sv.CombView.Aff.eval,
            LeanModels.Sv.CombView.Aff.evalTerms, LeanModels.Sv.CombView.Aff.sub,
            LeanModels.Sv.CombView.Aff.neg, LeanModels.Sv.CombView.Aff.negTerms,
            LeanModels.Sv.CombView.Aff.add, LeanModels.Sv.CombView.Aff.var,
            LeanModels.Sv.CombView.Aff.const, LeanModels.Sv.CombView.Aff.scale,
            LeanModels.Sv.CombView.Aff.scaleTerms, LeanModels.Sv.CombView.σL,
            LeanModels.Sv.CombView.Summary.val, LeanModels.Sv.CombView.lpEnv,
            LeanModels.Sv.CombView.CE.eval, List.lookup_cons, List.lookup_nil, $pdId:ident,
            List.zip_cons_cons, List.zip_nil_right, List.lookup_cons_self, Option.getD_some,
            $taskLemmas,*] <;> omega))
      catch e =>
        throwError "sv_interface: the declared ports do not match the task's interface (or the width arithmetic is outside `omega`'s reach):\n{e.toMessageData}"

@[tactic svInterface] unsafe def evalSvInterfaceL : Tactic := fun _ => guardL (withDeepRec runSvInterfaceL)

/-! ## `sv_equations` -/

private partial def countAndL (e : Expr) : Nat :=
  if e.isAppOfArity ``And 2 then 1 + countAndL e.appArg! else 1

private def eqNameL (ls : LSite) : String := s!"eq_{ls.site.tgt.name}_{ls.blk}_{ls.site.pos}"
private def knownNameL (ls : LSite) : String := s!"known_{ls.site.tgt.name}_{ls.blk}_{ls.site.pos}"

private def peelNamesL (h : Ident) (names : List String) : TacticM Unit := do
  match names with
  | [] => return
  | [n] =>
      evalTactic (← `(tactic| have $(mkIdent (Name.mkSimple n)) := $h))
      evalTactic (← `(tactic| clear $h))
  | n :: rest =>
      evalTactic (← `(tactic| obtain ⟨$(mkIdent (Name.mkSimple n)):ident, $h:ident⟩ := $h))
      peelNamesL h rest

unsafe def runSvEquationsL (hintOnly : Bool) : TacticM Unit := do
  let goal ← getMainGoal
  let saved ← saveState
  let report : Array String ← goal.withContext do
    let some (hlN, X) ← findLowerHyp | throwUnsupportedSyntax
    let mut heqs? : Option (Name × Expr) := none
    let mut hsh? : Option Name := none
    let mut hc? : Option Name := none
    let mut ha? : Option Name := none
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      let f := t.getAppFn
      if f.isConstOf ``LeanModels.Sv.CombEqs && heqs?.isNone then heqs? := some (d.userName, t)
      else if f.isConstOf ``LeanModels.Sv.StateShape && hsh?.isNone then hsh? := some d.userName
      else if f.isConstOf ``LeanModels.Sv.CombDesign && hc?.isNone then hc? := some d.userName
      else if f.isConstOf ``LeanModels.Sv.Acyclic && ha?.isNone then ha? := some d.userName
    let some (heqsN, _) := heqs?
      | throwError "sv_equations: no hypothesis `CombEqs d' st` in the context (the settled state of the lowered design: use the local bridge lemma, `intro st heqs hs …`)"
    let some hshN := hsh?
      | throwError "sv_equations: no hypothesis `StateShape d' st` in the context"
    let some hcN := hc?
      | throwError "sv_equations: no hypothesis `CombDesign d'` in the context (prove it with `sv_structure`)"
    let some haN := ha?
      | throwError "sv_equations: no hypothesis `Acyclic d'` in the context (prove it with `sv_structure (rank := …)`)"
    let some (pd, args) ← findGD2L X 8
      | throwError "sv_equations: cannot read a `load_design_sv2` family (`X.sem N`) off the design of `{hlN}`"
    let some pdName := headConstL? pd
      | throwError "sv_equations: the design is not a named constant"
    match ← evalSummaryP pd with
    | .error msg => throwError "sv_equations: outside the supported fragment — {msg}"
    | .ok s =>
      let probs := s.structProblems
      unless probs.isEmpty do
        throwError "sv_equations: structural check failed:\n  {"\n  ".intercalate probs}"
      let pdId := mkIdent pdName
      let keyI := mkIdent `key
      let hlI := mkIdent hlN
      let hcI := mkIdent hcN
      let haI := mkIdent haN
      let heqsI := mkIdent heqsN
      let hshI := mkIdent hshN
      evalTactic (← `(tactic|
        have $keyI:ident := LeanModels.Sv.CombEq.eq_viewL (s := ?s) (env := ?env) (hs := ?hs)
            (harity := ?harity) (h1 := ?h1) (hag := ?hag) (hok := ?hok) (hauto := ?hauto)
            (hin := ?hin) (hself := ?hself) (hfrag := ?hfrag) (hwid := ?hwid) (hbit := ?hbit)
            (hcov := ?hcov) (hinK := ?hinK) (hl := $hlI) (hc := $hcI) (ha := $haI)
            (heqs := $heqsI) (hsh := $hshI)))
      let goals ← getGoals
      let named : List Name := [`s, `env, `hs, `harity, `h1, `hag, `hok, `hauto, `hin, `hself,
        `hfrag, `hwid, `hbit, `hcov, `hinK]
      let mut bodyGoal? : Option MVarId := none
      for g in goals do
        unless named.contains (← g.getTag).eraseMacroScopes do
          if bodyGoal?.isNone then bodyGoal? := some g
      let some bodyGoal := bodyGoal?
        | throwError "sv_equations: internal error: no main goal after introducing the netlist view"
      let find (n : Name) : TacticM MVarId := do
        for g in goals do
          if (← g.getTag).eraseMacroScopes == n then return g
        throwError "sv_equations: internal error: goal `{n}` not found"
      let closeWith (n : Name) (what : String) (tac : TSyntax `tactic) : TacticM Unit := do
        setGoals [← find n]
        try
          evalTactic tac
        catch e =>
          throwError "sv_equations: {what}\n{e.toMessageData}"
        unless (← getGoals).isEmpty do
          throwError "sv_equations: {what}"
      let closeDecide (n : Name) (what : String) : TacticM Unit := do
        setGoals [← find n]
        try
          closeByDecide (← getMainGoal) what
          setGoals []
        catch _ =>
          closeWith n what (← `(tactic| decide +kernel))
      closeWith `hs "the recognizer's summary could not be computed by `rfl`" (← `(tactic| rfl))
      closeWith `harity "the number of arguments differs from the number of parameters" (← `(tactic| rfl))
      closeWith `h1 "the parameter stage (`paramEnv2`) of this design could not be evaluated at a symbolic parameter" (← `(tactic| rfl))
      closeWith `hag "the parameter values could not be read off the instantiation environment" (← `(tactic| rfl))
      closeDecide `hok "the structural check failed"
      closeDecide `hfrag "a right-hand side is outside the fragment of `sv_equations` (a gate tree of `&`, `|`, `^` over accesses and known literals, a concatenation of accesses and known literals, or a fill `'0`/`'1`; in an `always_comb`, the same at every leaf and a gate tree as the condition)"
      let mut out : Array MVarId := #[]
      let runOb (n : Name) (nm : String) (tac : TSyntax ``Lean.Parser.Tactic.tacticSeq) :
          TacticM (List MVarId) := do
        setGoals [← find n]
        try evalTactic tac
        catch e => throwError "sv_equations: while normalizing the obligation `{nm}`: {e.toMessageData}"
        let rest ← getGoals
        let k := rest.length
        let mut i := 0
        for g in rest do
          i := i + 1
          g.setTag (if k == 1 then Name.mkSimple nm else Name.mkSimple s!"{nm}_{i}")
        return rest
      out := out ++ (← runOb `hauto "auto" (← `(tacticSeq|
        (try simp only [$pdId:ident])
        svL_norm
        repeat' refine And.intro ?_ ?_
        all_goals first | (intros; omega) | skip))).toArray
      out := out ++ (← runOb `hin "inRange" (← `(tacticSeq|
        (try simp only [$pdId:ident])
        svL_norm
        repeat' refine And.intro ?_ ?_))).toArray
      out := out ++ (← runOb `hself "noSelfRead" (← `(tacticSeq|
        (try simp only [$pdId:ident])
        svL_norm
        repeat' refine And.intro ?_ ?_))).toArray
      out := out ++ (← runOb `hwid "width" (← `(tacticSeq|
        (try simp only [$pdId:ident])
        repeat (svL_eq_norm; try simp)
        repeat' refine And.intro ?_ ?_))).toArray
      out := out ++ (← runOb `hbit "bitRead" (← `(tacticSeq|
        (try simp only [$pdId:ident])
        repeat (svL_eq_norm; try simp)
        repeat' refine And.intro ?_ ?_))).toArray
      out := out ++ (← runOb `hcov "cover" (← `(tacticSeq|
        (try simp only [$pdId:ident])
        repeat (svL_eq_norm; try simp)
        repeat' refine And.intro ?_ ?_))).toArray
      out := out ++ (← runOb `hinK "inputsKnown" (← `(tacticSeq|
        (try simp only [$pdId:ident])
        repeat (svL_eq_norm; try simp)
        repeat' refine And.intro ?_ ?_))).toArray
      setGoals [bodyGoal]
      try evalTactic (← `(tactic| (try simp only [$pdId:ident] at $keyI:ident)))
      catch e => throwError "sv_equations: while unfolding the design in the netlist view: {e.toMessageData}"
      try evalTactic (← `(tactic| (repeat (svL_eq_norm_at $keyI))))
      catch e => throwError "sv_equations: while normalizing the netlist view: {e.toMessageData}"
      let sites := s.lsites
      let eqNames := sites.map eqNameL
      let knNames := sites.map knownNameL
      let kt ← instantiateMVars (← (← getMainGoal).withContext do
        let some d := (← getLCtx).findFromUserName? `key | throwError "sv_equations: internal error: no `key`"
        return d.type)
      let isAnd := kt.isAppOfArity ``And 2
      -- (as in `sv_equations`: the spine may be longer than the number of sites when the last site's
      -- own fact is a conjunction)
      let nE := if isAnd then countAndL kt.appFn!.appArg! else 0
      let nK := if isAnd then countAndL kt.appArg! else 0
      if isAnd && eqNames.length ≤ nE && knNames.length ≤ nK then
        evalTactic (← `(tactic| obtain ⟨$(mkIdent `keyE):ident, $(mkIdent `keyK):ident⟩ := $keyI))
        peelNamesL (mkIdent `keyE) eqNames
        peelNamesL (mkIdent `keyK) knNames
        let mainG ← getMainGoal
        let aliasHyps ← mainG.withContext do
          let lctx ← getLCtx
          let mut hyps : Array Hypothesis := #[]
          for (ae, oe, ak, ok) in stableAliases sites do
            for (a, o) in [(ae, oe), (ak, ok)] do
              if let some d := lctx.findFromUserName? (Name.mkSimple o) then
                hyps := hyps.push { userName := Name.mkSimple a, type := d.type, value := d.toExpr }
          return hyps
        let (_, mainG') ← mainG.assertHypotheses aliasHyps
        replaceMainGoal [mainG']
      else
        logWarning m!"sv_equations: the normalized netlist view has {nE} equation and {nK} knownness conjuncts for {eqNames.length} sites; left in `key` unnamed"
      let mut lines : Array String := #[]
      if hintOnly then
        let g ← getMainGoal
        let aliasNames := (stableAliases sites).foldl (fun acc (ae, _, ak, _) => acc ++ [ae, ak]) []
        lines ← g.withContext do
          let mut ls : Array String := #[]
          for d in ← getLCtx do
            if d.isImplementationDetail then continue
            let n := d.userName.toString
            if aliasNames.contains n then continue
            if n.startsWith "eq_" || n.startsWith "known_" || n == "key" then
              ls := ls.push s!"  {n} : {← ppExpr (← instantiateMVars d.type)}"
          if isAnd && eqNames.length ≤ nE && knNames.length ≤ nK then
            ls := ls.push "  stable aliases (copies of the above; same statements):"
            for (ae, oe, ak, ok) in stableAliases sites do
              ls := ls.push s!"    {ae} := {oe}    {ak} := {ok}"
          return ls
        for g in out do
          lines := lines.push s!"  [{(← g.getTag)}] ⊢ {← g.withContext (do ppExpr (← instantiateMVars (← g.getType)))}"
      else
        setGoals ((← getMainGoal) :: out.toList)
      return lines
  if hintOnly then
    saved.restore
    logInfo m!"sv_equations: the netlist view and the obligations (lowered design)\n  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)\n{"\n".intercalate report.toList}"

@[tactic svEquations] unsafe def evalSvEquationsL : Tactic := fun _ => guardL (withDeepRec (runSvEquationsL false))

@[tactic svEquationsQ] unsafe def evalSvEquationsQL : Tactic := fun _ => guardL (withDeepRec (runSvEquationsL true))
