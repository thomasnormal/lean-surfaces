import Lean
import LeanModels.Sv.CombViewTactic
import LeanModels.Sv.CombEqThm
import LeanModels.Sv.CombEqPlain
import LeanModels.Sv.CombBridge
import LeanModels.Sv.CombCover

/-!
# `sv_equations` / `sv_equations?` / `sv_cover`: the equations stage of the `sv_comb` tactic (v0)

```
theorem ripple_correct (N : Nat) (hN : 1 ≤ N) : ripple_add.sem N ⊨₂ spec2 … := by
  have hc : CombDesign (ripple_add.sem N) := by sv_structure; all_goals (intros; omega)
  have ha : Acyclic (ripple_add.sem N) := by sv_structure (rank := …); all_goals (intros; omega)
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y ci hA hB hCi
  sv_equations
  -- main goal first, with the equations of the netlist in the context:
  --   eq_c_plain_0    : st.boolAt "c" 0 = st.boolAt "cin" 0
  --   eq_cout_plain_1 : st.boolAt "cout" 0 = st.boolAt "c" N
  --   eq_s_g_bit_0    : ∀ i, i < N → st.boolAt "s" i = (… ^^ … ^^ …)
  --   eq_c_g_bit_1    : ∀ i, i < N → st.boolAt "c" (i + 1) = (… && …) || (… && (… ^^ …))
  -- and the knownness facts known_* ; then the OBLIGATIONS as further goals.
```

What `sv_equations` does. It reads the design off the settled-state hypotheses in the context
(`CombEqs`, `StateShape` of `X.sem N`) and the structural proofs (`CombDesign`, `Acyclic`, the
product of `sv_structure`), runs the recognizer (`PDesign.summary`, as `sv_structure`), applies the
producer theorem `CombEq.eq_view` (the parameter stage, the structural facts and the fragment check
are closed by `rfl` and `decide`), normalizes the netlist view `s.Eqs ∧ s.Knowns` to one named
hypothesis per assign (`eq_<signal>_<block>_<position>`, `known_…`; and the STABLE ALIASES
`eq_<signal>_<k>`, `known_<signal>_<k>`, `k` the ordinal of the assign among those that write the
signal: `stableAliases`), and returns the obligations it does not discharge, tagged. (The view has one
conjunct per site, in site order, and a site's knownness fact may itself be a conjunction, so the sites
are the first `n` conjuncts of each spine: the spine may be longer than `n` when the LAST site drives a
bit of a vector target. The tactic runs with `maxRecDepth` raised to 100000 (`withDeepRec`), so a netlist
of a hundred sites needs no `set_option maxRecDepth` in the player's file.)

* `auto`, `inRange` — as for `sv_structure` (reads/targets inside their declared vectors);
* `width` — every operand is exactly as wide as the target (no implicit `resize`);
* `bitRead` — a bit read lies inside its vector;
* `cover` — every bit a read observes has a source (an input bit or a bit some assign writes);
* `inputsKnown` — the input ports hold known vectors of their declared width (the player's premise:
  the tactic cannot know how the inputs were obtained).

**Flat netlists (WP-P3b).** When EVERY site is plain (no generate loop) and the design has no free
parameter, `auto`, `inRange`, `width`, `bitRead` and `cover` are closed, decidable statements about the site
list, and `sv_equations` DECIDES them (`closeByDecide` through `CombViewPlain.lean` and `CombEqPlain.lean`)
instead of normalizing them: no goal is returned for them, so the `cover_k` goals do not exist for such a
design and only the main goal and `inputsKnown` are left (`sv_equations?` says which obligations it decided).
Any failure (a loop, a parameter, a false statement) takes the normalization route and returns its goals as
before. The `always_comb` elaborator (`CombProcTactic.lean`) has no such path.

**Knownness.** Why the Boolean equations are the real semantics: in a state that solves the design's
equations, with the comb shape, known inputs, and a rank certificate, EVERY supported read is known
(`CombKnown.reads_known`, `CombKnownThm.lean`; its consequences `CombKnown.settled` for the driven bits are
what `known_*` states). A four-state gate of known bits is the Boolean gate, so the right-hand side
evaluates to a Boolean and `eq_*` holds. The producer theorem `CombEq.eq_view` cites it through
`CombKnown.settled`; a construct whose value is not determined by the Boolean values of its reads needs
the same hypothesis and gets it from the same theorem.

The equations are over `Bool` (`SvState.boolAt`), with the SV's gate structure preserved
(left-associated `^`); the row stride of a 2-D signal hides inside `rmN W i j`. The simp set that
normalizes them is `simp only`: the shapes are never reshaped by the full simp set (it would turn
`a ^^ b ^^ c` into `a != (b != c)`).

`sv_equations?` prints the equations and the obligations and changes nothing.

`sv_cover` is the player's explicit helper for `cover` goals (it is not part of `sv_equations`):
`omega`, a classical case split on each disjunct, and a bounded search for the witnesses of the
existentials among the local variables and the row/column terms of the read. It closes every
one-dimensional coverage goal and the simple two-dimensional ones; the nested two-dimensional goals
of the array multiplier exceed its (deliberately small) search budget and are closed by hand in
`Examples/system-verilog/mul_array/comb_proof.lean`.
-/

open Lean Elab Tactic Meta
open LeanModels.Sv.CombView

/-- `X.sem N` is `PDesign.instantiateGD2 X.pdesign [↑N]`: unfold until it shows. -/
private partial def findGD2' (e : Expr) (fuel : Nat) : MetaM (Option (Expr × Expr)) := do
  let e ← whnfCore e
  if e.isAppOfArity ``LeanModels.Sv.PDesign.instantiateGD2 2 then
    return some (e.getAppArgs[0]!, e.getAppArgs[1]!)
  match fuel with
  | 0 => return none
  | fuel + 1 =>
    match ← unfoldDefinition? e with
    | some e' => findGD2' e' fuel
    | none => return none

/-- The normalization of the netlist view (a hypothesis `at`), extending `sv_norm_core`'s set with
the equation vocabulary. -/
macro "sv_eq_norm_at" h:ident : tactic =>
  `(tactic| (simp (config := { maxSteps := 4000000 }) only [LeanModels.Sv.CombView.Summary.val, LeanModels.Sv.CombView.lpEnv, List.lookup_cons, List.lookup_nil, LeanModels.Sv.CombView.CE.eval,
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
      LeanModels.Sv.CombEq.LoopsE, LeanModels.Sv.CombEq.accBitUpper, LeanModels.Sv.CombEq.Sk.WidthOk, LeanModels.Sv.CombEq.Sk.SelfOk, LeanModels.Sv.CombEq.Sk.width,
      LeanModels.Sv.XF.red, LeanModels.Sv.XF.any_one, LeanModels.Sv.XF.eqv_one,
      LeanModels.Sv.CombEq.Part.wid, LeanModels.Sv.CombEq.Part.bit] at $h:ident; sv_lp_norm_at $h))

/-- … on the goal (for the obligations that mention the new vocabulary). -/
macro "sv_eq_norm" : tactic =>
  `(tactic| (simp (config := { maxSteps := 4000000 }) only [LeanModels.Sv.CombView.Summary.val, LeanModels.Sv.CombView.lpEnv, List.lookup_cons, List.lookup_nil, LeanModels.Sv.CombView.CE.eval,
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
      LeanModels.Sv.CombEq.LoopsE, LeanModels.Sv.CombEq.accBitUpper, LeanModels.Sv.CombEq.Sk.WidthOk, LeanModels.Sv.CombEq.Sk.SelfOk, LeanModels.Sv.CombEq.Sk.width,
      LeanModels.Sv.XF.red, LeanModels.Sv.XF.any_one, LeanModels.Sv.XF.eqv_one,
      LeanModels.Sv.CombEq.Part.wid, LeanModels.Sv.CombEq.Part.bit]; sv_lp_norm))

/-- The number of conjuncts of a right-nested `∧` (on the right spine: a conjunct that is itself a
conjunction counts once, except the LAST one, whose own parts continue the spine). -/
private partial def countAnd (e : Expr) : Nat :=
  if e.isAppOfArity ``And 2 then 1 + countAnd e.appArg! else 1

private def eqName (ls : LSite) : String := s!"eq_{ls.site.tgt.name}_{ls.blk}_{ls.site.pos}"
private def knownName (ls : LSite) : String := s!"known_{ls.site.tgt.name}_{ls.blk}_{ls.site.pos}"

/-- **Stable aliases** (WP-P, P2). The generated names `eq_<signal>_<block>_<position>` depend on the
generate-block label and on the assign's position in its block, so an unrelated edit (a renamed label,
an assign added above) renumbers them. The aliases name an equation by its TARGET signal and the
ordinal (from 1) of the assign among the assigns that write that signal, in source order:
`eq_c_1` is the first assign that writes `c`, `eq_c_2` the second. An edit that does not add, remove or
reorder the assigns of a signal leaves that signal's aliases alone. For each site: the alias of the
equation, of the knownness fact, and the generated names they stand for. -/
def stableAliases (sites : List LSite) : List (String × String × String × String) := Id.run do
  let mut counts : List (String × Nat) := []
  let mut out : List (String × String × String × String) := []
  for ls in sites do
    let n := ls.site.tgt.name
    let k := ((counts.lookup n).getD 0) + 1
    counts := (n, k) :: counts.filter (·.1 != n)
    out := out ++ [(s!"eq_{n}_{k}", eqName ls, s!"known_{n}_{k}", knownName ls)]
  return out

/-- Peel a right-nested conjunction `h : A₁ ∧ … ∧ Aₖ` into the named hypotheses. -/
private def peelNames (h : Ident) (names : List String) : TacticM Unit := do
  match names with
  | [] => return
  | [n] =>
      evalTactic (← `(tactic| have $(mkIdent (Name.mkSimple n)) := $h))
      evalTactic (← `(tactic| clear $h))
  | n :: rest =>
      evalTactic (← `(tactic| obtain ⟨$(mkIdent (Name.mkSimple n)):ident, $h:ident⟩ := $h))
      peelNames h rest

/-- Run the equations stage. (`unsafe`: it evaluates the recognizer with `evalExpr`.) -/
unsafe def runSvEquationsCore (hintOnly : Bool) : TacticM Unit := do
  let goal ← getMainGoal
  let saved ← saveState
  let report : Array String ← goal.withContext do
    -- the hypotheses the stage needs, by type
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
    let some (heqsN, heqsT) := heqs?
      | throwError "sv_equations: no hypothesis `CombEqs (X.sem N) st` in the context (the settled state: use `Models2.of_comb_pointwise` and `intro st heqs hsh …`)"
    let some hshN := hsh?
      | throwError "sv_equations: no hypothesis `StateShape (X.sem N) st` in the context"
    let some hcN := hc?
      | throwError "sv_equations: no hypothesis `CombDesign (X.sem N)` in the context (prove it with `sv_structure`)"
    let some haN := ha?
      | throwError "sv_equations: no hypothesis `Acyclic (X.sem N)` in the context (prove it with `sv_structure (rank := …)`)"
    let D := heqsT.appFn!.appArg!
    let some (pd, args) ← findGD2' D 8
      | throwError "sv_equations: cannot read a `load_design_sv2` family (`X.sem N`) off the design of `{heqsN}`"
    let some pdName := (match pd.getAppFn with | .const n _ => some n | _ => none)
      | throwError "sv_equations: the design is not a named constant"
    match ← evalSummary pd with
    | .error msg => throwError "sv_equations: outside the supported fragment — {msg}"
    | .ok s =>
      let probs := s.structProblems
      unless probs.isEmpty do
        throwError "sv_equations: structural check failed:\n  {"\n  ".intercalate probs}"
      let pdId := mkIdent pdName
      let keyI := mkIdent `key
      let hcI := mkIdent hcN
      let haI := mkIdent haN
      let heqsI := mkIdent heqsN
      let hshI := mkIdent hshN
      evalTactic (← `(tactic|
        have $keyI:ident := LeanModels.Sv.CombEq.eq_view (s := ?s) (env := ?env) (hs := ?hs)
            (harity := ?harity) (h1 := ?h1) (hag := ?hag) (hok := ?hok) (hauto := ?hauto)
            (hin := ?hin) (hfrag := ?hfrag) (hwid := ?hwid) (hbit := ?hbit) (hcov := ?hcov)
            (hinK := ?hinK) (hc := $hcI) (ha := $haI) (heqs := $heqsI) (hsh := $hshI)))
      let goals ← getGoals
      let named : List Name := [`s, `env, `hs, `harity, `h1, `hag, `hok, `hauto, `hin, `hfrag, `hwid,
        `hbit, `hcov, `hinK]
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
          -- false (or not evaluable): the kernel decision, for its own report, as before WP-P
          closeWith n what (← `(tactic| decide +kernel))
      closeWith `hs "the recognizer's summary could not be computed by `rfl`" (← `(tactic| rfl))
      closeWith `harity "the number of arguments differs from the number of parameters" (← `(tactic| rfl))
      closeWith `h1 "the parameter stage (`paramEnv2`) of this design could not be evaluated at a symbolic parameter" (← `(tactic| rfl))
      closeWith `hag "the parameter values could not be read off the instantiation environment" (← `(tactic| rfl))
      closeDecide `hok "the structural check failed"
      closeDecide `hfrag "a right-hand side is outside the fragment of `sv_equations` (an expression over accesses and known literals built from `& | ^`, `~ !`, the reductions, `&& ||`, `== !=` and `?:`, a concatenation of accesses and known literals, or a fill `'0`/`'1`)"
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
      -- A FLAT netlist (all sites plain, no parameter; WP-P3b): the five obligations below are closed
      -- statements about the site list. They are DECIDED (`tryClosePlain`, the lemmas of `CombViewPlain`
      -- and `CombEqPlain`) instead of normalized, and no goal is returned for them; `decided` records
      -- which, for the hint. Any failure takes the normalization route and returns its goals as before.
      let mut decided : Array String := #[]
      if (← tryClosePlain s (← find `hauto) ``LeanModels.Sv.CombView.Summary.autoObl_of_plain
          "an in-range fact of a flat netlist does not hold") then
        decided := decided.push "auto"
      else
        out := out ++ (← runOb `hauto "auto" (← `(tacticSeq|
          (try simp only [$pdId:ident])
          sv_norm
          repeat' refine And.intro ?_ ?_
          all_goals first | (intros; omega) | skip))).toArray
      if (← tryClosePlain s (← find `hin) ``LeanModels.Sv.CombView.Summary.inRangeObl_of_plain
          "the in-range obligation of a flat netlist does not hold") then
        decided := decided.push "inRange"
      else
        out := out ++ (← runOb `hin "inRange" (← `(tacticSeq|
          (try simp only [$pdId:ident])
          sv_norm
          repeat' refine And.intro ?_ ?_))).toArray
      if (← tryClosePlain s (← find `hwid) ``LeanModels.Sv.CombView.Summary.widthObl_of_plain
          "an operand of a flat netlist is not as wide as its target") then
        decided := decided.push "width"
      else
        out := out ++ (← runOb `hwid "width" (← `(tacticSeq|
          (try simp only [$pdId:ident])
          repeat (sv_eq_norm; try simp)
          repeat' refine And.intro ?_ ?_))).toArray
      if (← tryClosePlain s (← find `hbit) ``LeanModels.Sv.CombView.Summary.bitReadObl_of_plain
          "a bit read of a flat netlist is outside its vector") then
        decided := decided.push "bitRead"
      else
        out := out ++ (← runOb `hbit "bitRead" (← `(tacticSeq|
          (try simp only [$pdId:ident])
          repeat (sv_eq_norm; try simp)
          repeat' refine And.intro ?_ ?_))).toArray
      if (← tryClosePlain s (← find `hcov) ``LeanModels.Sv.CombView.Summary.coverObl_of_plain
          "a bit read by a flat netlist has no source") then
        decided := decided.push "cover"
      else
        out := out ++ (← runOb `hcov "cover" (← `(tacticSeq|
          (try simp only [$pdId:ident])
          repeat (sv_eq_norm; try simp)
          repeat' refine And.intro ?_ ?_))).toArray
      out := out ++ (← runOb `hinK "inputsKnown" (← `(tacticSeq|
        (try simp only [$pdId:ident])
        repeat (sv_eq_norm; try simp)
        repeat' refine And.intro ?_ ?_))).toArray
      -- the netlist view, one named hypothesis per site
      setGoals [bodyGoal]
      try evalTactic (← `(tactic| (try simp only [$pdId:ident] at $keyI:ident)))
      catch e => throwError "sv_equations: while unfolding the design in the netlist view: {e.toMessageData}"
      try evalTactic (← `(tactic| (repeat (sv_eq_norm_at $keyI))))
      catch e => throwError "sv_equations: while normalizing the netlist view: {e.toMessageData}"
      let sites := s.lsites
      let eqNames := sites.map eqName
      let knNames := sites.map knownName
      let kt ← instantiateMVars (← (← getMainGoal).withContext do
        let some d := (← getLCtx).findFromUserName? `key | throwError "sv_equations: internal error: no `key`"
        return d.type)
      let isAnd := kt.isAppOfArity ``And 2
      let nE := if isAnd then countAnd kt.appFn!.appArg! else 0
      let nK := if isAnd then countAnd kt.appArg! else 0
      -- The view has one conjunct per site, in site order, so the sites are the first `n` conjuncts of
      -- each spine: the spine may be LONGER than `n` when the last site's own fact is a conjunction (a
      -- bit of a vector target states `∃ v, … ∧ …` and `KnownBit …`: two spine nodes for one site).
      -- `peelNames` takes the first `n - 1` by `obtain` and leaves the rest as the last hypothesis.
      if isAnd && eqNames.length ≤ nE && knNames.length ≤ nK then
        evalTactic (← `(tactic| obtain ⟨$(mkIdent `keyE):ident, $(mkIdent `keyK):ident⟩ := $keyI))
        peelNames (mkIdent `keyE) eqNames
        peelNames (mkIdent `keyK) knNames
        -- the stable aliases: copies of the generated hypotheses under `eq_<signal>_<k>`, asserted
        -- directly (`assertHypotheses`: no elaboration, so a heartbeat-tight `solution` is not tipped over)
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
        unless decided.isEmpty do
          lines := lines.push s!"  decided (flat netlist: every site plain, no parameter): {", ".intercalate decided.toList}"
        for g in out do
          lines := lines.push s!"  [{(← g.getTag)}] ⊢ {← g.withContext (do ppExpr (← instantiateMVars (← g.getType)))}"
      else
        setGoals ((← getMainGoal) :: out.toList)
      return lines
  if hintOnly then
    saved.restore
    logInfo m!"sv_equations: the netlist view and the obligations\n  (Boolean equations: every supported read is known in a settled state, `CombKnown.reads_known`)\n{"\n".intercalate report.toList}"

/-- `sv_equations` — see the module docstring. -/
syntax (name := svEquations) "sv_equations" : tactic

/-- `sv_equations?` prints the equations and obligations it would produce, and changes nothing. -/
syntax (name := svEquationsQ) "sv_equations?" : tactic

/-- `sv_equations`, run with the deep recursion limit of `withDeepRec`: the normalization of a view of a
hundred sites recurses once per site. -/
unsafe def runSvEquations (hintOnly : Bool) : TacticM Unit := withDeepRec (runSvEquationsCore hintOnly)

@[tactic svEquations] unsafe def evalSvEquations : Tactic := fun _ => runSvEquations false

@[tactic svEquationsQ] unsafe def evalSvEquationsQ : Tactic := fun _ => runSvEquations true

/-! ## `sv_cover`: the coverage helper

A coverage goal says that a bit a read observes has a source: `A ∨ B ∨ ∃ j, …` with linear
constraints. `sv_cover` is the player's explicit call (it is NOT part of `sv_equations`): it closes
such a goal by `omega`, by choosing a side of a disjunction, and by trying as witness each local
`Nat`/`Int` variable shifted by a small constant (`x`, `x - 1`, `x + 1`, `x - 2`, `x + 2`), the
remaining constraints going to `omega`.

**The 2-D rule** (WP-P4, `CombCover.lean`; tried first). For the cell reads of a 2-D array it solves
each `∃`-variable from the affine equations of the read's row and column (`a := (R - r₀).toNat`, with
a division and the parity left to `omega` when the loop steps by 2), states the writer's condition at
those witnesses and walks the disjunction of writers: `Classical.em` of the condition, the proof built
from its components, `omega` on the last writer. A shape it does not read falls through to the search
below; a goal it reads and cannot prove is reported with the read and the conditions each writer needs.

**Site witnesses** (WP-P3b). When the source of a bit is a SITE (`∃ b, (b = site₀ ∨ … ∨ b = siteₘ₋₁) ∧
Q b`, what a netlist of more than a few dozen plain sites leaves after the normalization), `sv_cover`
picks the writer by NAME: it keeps the sites whose target is the signal `Q` names (`b.site.tgt.name =
"y14"`, read off the site's constructor term, no evaluation), builds the membership proof in the
disjunction directly and closes the rest of `Q` with `decide` (`omega` when a parameter is free). The
input-bit disjunct `A ∨ …` is tried first. A design with no generate loop and no parameter never reaches
this: `sv_equations` has already decided its coverage (`CombEqPlain.lean`). -/

/-- Try the alternatives in order, restoring the state after a failure; the error is the last one. -/
private partial def firstOf (alts : List (TacticM Unit)) : TacticM Unit := do
  match alts with
  | [] => throwError "sv_cover: no alternative closes the goal"
  | [a] => a
  | a :: rest =>
      let st ← saveState
      try a
      catch _ =>
        st.restore
        firstOf rest

/-- The row and column terms of every `rmN W r c` in `e` that mentions no bound variable (the
READ position of a coverage goal: the windows of the writers mention the existential variables). -/
private partial def closedRmNArgs (e : Expr) : List Expr :=
  if e.isAppOfArity ``LeanModels.Sv.CombView.rmN 3 then
    if e.hasLooseBVars then [] else [e.getArg! 1, e.getArg! 2]
  else match e with
    | .app f a => closedRmNArgs f ++ closedRmNArgs a
    | .lam _ t b _ => closedRmNArgs t ++ closedRmNArgs b
    | .forallE _ t b _ => closedRmNArgs t ++ closedRmNArgs b
    | .letE _ t v b _ => closedRmNArgs t ++ closedRmNArgs v ++ closedRmNArgs b
    | .mdata _ b => closedRmNArgs b
    | .proj _ _ b => closedRmNArgs b
    | _ => []

/-- Candidate witnesses for an existential over `Nat` or `Int`: constants, the local variables of
either type, and the row and column terms of the READ position of the goal (with `± 1`), converted
(`(x + c).toNat`, `(↑x : Int) + c`). Duplicates are removed. -/
private def coverWitnesses (ty : Expr) (goalTy : Expr) : TacticM (List Expr) := do
  let intTy := mkConst ``Int
  let natTy := mkConst ``Nat
  let mut out : Array Expr := #[]
  let mut bases : List (Expr × Expr × Bool) := []   -- (term, its type, shift it by ±1)
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let dt ← whnfR (← instantiateMVars d.type)
    if dt == natTy || dt == intTy then bases := bases ++ [(d.toExpr, dt, true)]
  for a in closedRmNArgs goalTy do
    bases := bases ++ [(a, intTy, true)]
  for k in [0, 1] do
    out := out.push (← mkAppOptM ``OfNat.ofNat #[ty, mkRawNatLit k, none])
  for (x, dt, shift) in bases do
    let ks := if shift then [1] else []
    if dt == ty then
      out := out.push x
      for k in ks do
        let c ← mkAppOptM ``OfNat.ofNat #[ty, mkRawNatLit k, none]
        out := out.push (← mkAppM ``HSub.hSub #[x, c])
        out := out.push (← mkAppM ``HAdd.hAdd #[x, c])
    else if ty == natTy && dt == intTy then
      out := out.push (← mkAppM ``Int.toNat #[x])
      for k in ks do
        let c ← mkAppOptM ``OfNat.ofNat #[intTy, mkRawNatLit k, none]
        out := out.push (← mkAppM ``Int.toNat #[← mkAppM ``HSub.hSub #[x, c]])
        out := out.push (← mkAppM ``Int.toNat #[← mkAppM ``HAdd.hAdd #[x, c]])
    else if ty == intTy && dt == natTy then
      let xi ← mkAppOptM ``Nat.cast #[intTy, none, x]
      out := out.push xi
      for k in ks do
        let c ← mkAppOptM ``OfNat.ofNat #[intTy, mkRawNatLit k, none]
        out := out.push (← mkAppM ``HSub.hSub #[xi, c])
        out := out.push (← mkAppM ``HAdd.hAdd #[xi, c])
  let mut uniq : Array Expr := #[]
  for e in out do
    unless uniq.contains e do uniq := uniq.push e
  return uniq.toList

/-- One `sv_cover` call may spend this many leaf attempts (the search is bounded). -/
private def spendBudget (budget : IO.Ref Nat) : TacticM Unit := do
  let n ← budget.get
  if n == 0 then throwError "sv_cover: search budget exhausted"
  budget.set (n - 1)

/-! The existential spine `∃ x, G ∧ … ∧ ∃ y, H ∧ …` of a coverage disjunct, instantiated at a
tuple of witnesses: the quantifier-free proposition (`instSpine`) and the term that proves the
existential from a proof of it (`proofSpine`). -/

private partial def instSpine (e : Expr) (ws : List Expr) : Option Expr :=
  if e.isAppOfArity ``Exists 2 then
    match ws, e.appArg! with
    | w :: ws', .lam _ _ b _ => instSpine (b.instantiate1 w) ws'
    | _, _ => none
  else if e.isAppOfArity ``And 2 then
    match instSpine e.appArg! ws with
    | some r => some (mkApp2 (mkConst ``And) e.appFn!.appArg! r)
    | none => none
  else if ws.isEmpty then some e else none

private partial def proofSpine (e : Expr) (ws : List Expr) (h : Term) : TacticM Term := do
  if e.isAppOfArity ``Exists 2 then
    match ws, e.appArg! with
    | w :: ws', .lam _ _ b _ =>
        let wS ← Term.exprToSyntax w
        let rest ← proofSpine (b.instantiate1 w) ws' h
        `(⟨$wS, $rest⟩)
    | _, _ => throwError "sv_cover: internal error (spine)"
  else if e.isAppOfArity ``And 2 then
    let rest ← proofSpine e.appArg! ws (← `($h.2))
    `(⟨$h.1, $rest⟩)
  else return h

/-- Number of nested existentials on the spine of `e`. -/
private partial def spineDepth (e : Expr) : Nat :=
  if e.isAppOfArity ``Exists 2 then
    match e.appArg! with
    | .lam _ _ b _ => 1 + spineDepth b
    | _ => 1
  else if e.isAppOfArity ``And 2 then spineDepth e.appArg!
  else 0

/-- The binder types along the spine. -/
private partial def spineTypes (e : Expr) : List Expr :=
  if e.isAppOfArity ``Exists 2 then
    match e.appArg! with
    | .lam _ t b _ => t :: spineTypes b
    | _ => []
  else if e.isAppOfArity ``And 2 then spineTypes e.appArg!
  else []

/-- All tuples picking one candidate per level. -/
private def tuplesOf : List (List Expr) → List (List Expr)
  | [] => [[]]
  | cs :: rest => cs.flatMap fun c => (tuplesOf rest).map (c :: ·)

/-- The right-hand sides `c₀ … cₘ₋₁` of a membership disjunction `b = c₀ ∨ … ∨ b = cₘ₋₁`, or `none` if `e`
has another shape. -/
private partial def memDisjuncts (e : Expr) : Option (List Expr) :=
  let leaf (x : Expr) : Option Expr :=
    -- `b = c` with `b` the bound variable and `c` a closed term
    if x.isAppOfArity ``Eq 3 && x.appFn!.appArg! == .bvar 0 && !x.appArg!.hasLooseBVars then some x.appArg! else none
  if e.isAppOfArity ``Or 2 then
    match leaf e.appFn!.appArg!, memDisjuncts e.appArg! with
    | some c, some rest => some (c :: rest)
    | _, _ => none
  else (leaf e).map ([·])

/-- The proof that the `i`-th disjunct of `e` (a membership disjunction already instantiated at `w`) holds:
`Or.inr (… (Or.inl rfl))`, the last one `Or.inr (… rfl)`. -/
private partial def memProof (e : Expr) (i : Nat) (w : Expr) : MetaM Expr := do
  if e.isAppOfArity ``Or 2 then
    let a := e.appFn!.appArg!
    let b := e.appArg!
    match i with
    | 0 => return mkApp3 (mkConst ``Or.inl) a b (← mkEqRefl w)
    | i + 1 => return mkApp3 (mkConst ``Or.inr) a b (← memProof b i w)
  else mkEqRefl w

/-- The signal a site writes, read off its constructor term `LSite.mk hdrs blk (TSite.mk pos tgt rds proc)`
with `tgt` an `Acc` constructor whose first argument is the name literal. -/
private def siteTgtName? (c : Expr) : Option String :=
  let cs := c.getAppArgs
  if cs.size != 3 then none else
  let ts := cs[2]!.getAppArgs
  if ts.size != 4 then none else
  match ts[1]!.getAppArgs[0]? with
  | some (Expr.lit (Literal.strVal s)) => some s
  | _ => none

/-- Close the rest `Q w` of a site-witness cover: unfold the (empty) loop quantifier, then `decide` (a design
without a free variable), or the normalization of `sv_equations` (`sv_eq_norm`, with the declarations
evaluated), which closes the closed arithmetic that a parameter-carrying `σ` leaves, or `omega`. -/
private def closeSiteRest : TacticM Unit := do
  try evalTactic (← `(tactic| simp only [LeanModels.Sv.CombEq.LoopsE])) catch _ => pure ()
  unless (← getGoals).isEmpty do
    evalTactic (← `(tactic| first | decide | (repeat (sv_eq_norm; try simp); done) | omega))

/-- **The site witness**: for `∃ b, (b = c₀ ∨ … ∨ b = cₘ₋₁) ∧ Q b` (possibly after an input-bit disjunct
`A ∨ …`, tried first), pick the site by the name `Q` states and close `Q`. Fails (without effect) on any
other shape, so the general search below takes over. -/
private partial def siteWitness : TacticM Unit := do
  let goal ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  if ty.isAppOfArity ``Or 2 then
    -- the input-bit disjunct: `4 < ↑(Int.natAbs 7) + 1` and the like
    let st ← saveState
    try
      evalTactic (← `(tactic| refine Or.inl ?_))
      evalTactic (← `(tactic| first | decide | omega))
      unless (← getGoals).isEmpty do throwError "sv_cover: input disjunct left open"
      return
    catch _ => st.restore
    evalTactic (← `(tactic| refine Or.inr ?_))
    siteWitness
  else if ty.isAppOfArity ``Exists 2 then
    let .lam _ α body _ := ty.appArg! | throwError "sv_cover: not a site witness"
    unless body.isAppOfArity ``And 2 do throwError "sv_cover: not a site witness"
    let memB := body.appFn!.appArg!
    let qB := body.appArg!
    let some cs := memDisjuncts memB | throwError "sv_cover: not a site witness"
    if cs.length < 2 then throwError "sv_cover: not a site witness"
    -- the name `Q` states: its first conjunct is `<name of b> = "sig"`
    let want? : Option String :=
      let q1 := if qB.isAppOfArity ``And 2 then qB.appFn!.appArg! else qB
      if q1.isAppOfArity ``Eq 3 then
        match q1.appArg! with
        | Expr.lit (Literal.strVal s) => some s
        | _ => none
      else none
    let lvl := ty.getAppFn.constLevels!
    let mut idx : List Nat := []
    for (c, i) in cs.zipIdx do
      let ok := match want?, siteTgtName? c with
        | some w, some n => n == w
        | _, _ => true
      if ok then idx := idx ++ [i]
    for i in idx do
      let c := cs[i]!
      let st ← saveState
      try
        let mem := memB.instantiate1 c
        let q := qB.instantiate1 c
        let qm ← mkFreshExprSyntheticOpaqueMVar q
        let pf ← memProof mem i c
        goal.assign (mkApp4 (mkConst ``Exists.intro lvl) α ty.appArg! c
          (mkApp4 (mkConst ``And.intro) mem q pf qm))
        setGoals [qm.mvarId!]
        closeSiteRest
        unless (← getGoals).isEmpty do throwError "sv_cover: site witness left open"
        return
      catch _ => st.restore
    throwError "sv_cover: no site writes the bit"
  else throwError "sv_cover: not a site witness"

private partial def svCover (budget : IO.Ref Nat) : TacticM Unit := do
  firstOf [
    do spendBudget budget; siteWitness,
    do spendBudget budget; evalTactic (← `(tactic| omega)),
    -- 2-D leaves: witnesses cast back, row-major comparisons lexicographic, then `omega`
    do
      spendBudget budget
      evalTactic (← `(tactic| (try simp (disch := omega) only [Int.toNat_of_nonneg,
        LeanModels.Sv.CombView.rmN_add_col, LeanModels.Sv.CombView.rmN_lt_iff,
        LeanModels.Sv.CombView.rmN_le_iff, Int.toNat_natCast, Int.natCast_zero,
        Int.natCast_one, true_and, and_true, eq_self] at *)))
      evalTactic (← `(tactic| first | done | omega)),
    do
      let goal ← getMainGoal
      let ty ← whnfR (← instantiateMVars (← goal.getType))
      if ty.isAppOfArity ``Or 2 then
        let A := ty.appFn!.appArg!
        if spineDepth A == 0 && !A.isAppOfArity ``Or 2 then
          -- a quantifier-free `A`: the case `A` is closed by itself; in the case `¬A` prove `B`
          let aS ← goal.withContext (Term.exprToSyntax A)
          evalTactic (← `(tactic| refine (Classical.em $aS).elim (fun h => Or.inl h)
            (fun h => Or.inr ?_)))
          svCover budget
        else
          firstOf [
            -- the left disjunct outright
            do evalTactic (← `(tactic| refine Or.inl ?_)); svCover budget,
            -- an existential `A`: split on `A` at each tuple of candidate witnesses
            do
              let tys := spineTypes A
              let mut cs : List (List Expr) := []
              for t in tys do
                cs := cs ++ [← goal.withContext (coverWitnesses t ty)]
              firstOf ((tuplesOf cs).map fun ws => do
                match instSpine A ws with
                | none => throwError "sv_cover: skip"
                | some Aw =>
                    let awS ← goal.withContext (Term.exprToSyntax Aw)
                    let hI := mkIdent `hSvc
                    let prf ← goal.withContext (proofSpine A ws (← `($hI)))
                    evalTactic (← `(tactic| refine (Classical.em $awS).elim
                      (fun $hI => Or.inl $prf) (fun h => Or.inr ?_)))
                    svCover budget),
            -- the right disjunct outright
            do evalTactic (← `(tactic| refine Or.inr ?_)); svCover budget ]
      else if ty.isAppOfArity ``And 2 then
        evalTactic (← `(tactic| refine And.intro ?_ ?_))
        for g in ← getGoals do
          setGoals [g]
          svCover budget
        setGoals []
      else if ty.isAppOfArity ``Exists 2 then
        let wt := ty.appFn!.appArg!
        let ws ← goal.withContext (coverWitnesses wt ty)
        firstOf (ws.map fun w => do
          let wS ← (← getMainGoal).withContext (Term.exprToSyntax w)
          evalTactic (← `(tactic| refine ⟨$wS, ?_⟩))
          svCover budget)
      else throwError "sv_cover: not a coverage goal: {ty}" ]

/-- `sv_cover` closes a coverage goal (`A ∨ ∃ j, …` with linear constraints); see above. -/
syntax (name := svCoverStx) "sv_cover" : tactic

@[tactic svCoverStx] def evalSvCover : Tactic := fun _ => withDeepRec do
  let budget ← IO.mkRef 250
  try evalTactic (← `(tactic| intros)) catch _ => pure ()
  -- the 2-D rule first (`CombCover.lean`); a shape it does not read takes the search below
  let st ← saveState
  let done ← try LeanModels.Sv.CombCover.coverCells; pure true
    catch e =>
      if (← e.toMessageData.toString).startsWith LeanModels.Sv.CombCover.diagPrefix then throw e
      st.restore
      pure false
  unless done do svCover budget
