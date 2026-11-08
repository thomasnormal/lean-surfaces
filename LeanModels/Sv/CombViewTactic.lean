import Lean
import LeanModels.Sv.CombViewDiag
import LeanModels.Sv.CombCoreSimp
import LeanModels.Sv.CombViewPlain
import LeanModels.Sv.CombViewGroup
import LeanModels.Sv.CombShared
import LeanModels.Sv.CombAliasInert

/-!
# `sv_structure` / `sv_structure?`: the structural stage of the `sv_comb` tactic (v0)

```
theorem ripple_comb (N : Nat) (hN : 1 ≤ N) : CombDesign (ripple_add.sem N) := by
  sv_structure
  -- leaves ONLY the driver-window disjointness and in-range goals, as compact `∀`s
theorem ripple_acyclic (N : Nat) (hN : 1 ≤ N) : Acyclic (ripple_add.sem N) := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
  -- leaves the in-range / disjointness goals and the rank-decrease goals
theorem mul_acyclic (N : Nat) (hN : 1 ≤ N) : Acyclic (mul_n.sem N) := by
  sv_structure (lexRank := fun | .plain 0 => (0, 1, 0) | … | .fam "g_bit" 0 [i, j] => (i.toNat, j.toNat + 1, 1) …)
  -- the rank is a LEXICOGRAPHIC key (row, column, phase) over site identities
theorem mul_acyclic' (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (mul_n.sem N)) : Acyclic (mul_n.sem N) := by
  sv_structure using hc (lexRank := …)   -- the in-range and one-driver goals are not asked again
theorem ripple_struct (N : Nat) (hN : 1 ≤ N) : CombDesign (ripple_add.sem N) ∧ Acyclic (ripple_add.sem N) := by
  sv_structure (rank := rippleRank …)   -- ONE round of obligations for both (WP-P): `obtain ⟨hc, ha⟩ := ripple_struct N hN`
sv_structure?            -- prints the families, site identities and the required rank relation
```

What it does: reads the design off the goal (`X.sem N` is `PDesign.instantiateGDAlias2 X.pdesign [↑N]`, the
`always_comb` alias guard over `PDesign.instantiateGD2 X.pdesign [↑N]`; the goal is restated at the latter, the guard
shown inert by a static check, `CombAliasInert.lean`), runs the recognizer `PDesign.summary` (a refusal is an error
with the specific reason, naming the site), applies the theorem `comb_view`/`acyclic_view` (whose hypotheses are
CHECKED by `rfl` and `decide`: the parameter stage, the structural facts, the fuel; at a symbolic `int` parameter
the exact 32-bit reading of the parameters is checked against the summary's valuation from the range premises in
context, `closeHag`), normalizes the player
obligations, and returns them. It never discharges the in-range, disjointness or rank goals of a
design with a generate loop or a parameter. Before returning them it SAMPLES them at small `N` (for the
message only): a genuine violation is reported with the offending sites instead of an unprovable goal.

**Flat netlists (WP-P3b).** When EVERY site is plain (no generate loop) and the design has no free
parameter, the four obligations (`hauto`, `hin`, `hdisj`, `hrank`) are closed statements about the site
list, and the tactic DECIDES them (`closeByDecide`, through `CombViewPlain.lean`) instead of normalizing
them with `simp`, whose cost is quadratic in the number of sites for the one-driver and rank
obligations (4 min and a failure at 113 sites; about 12 s and 120 M heartbeats now, linear). Nothing is
left to the player in that case (not even the rank goals `rank[4] < rank[5]`). A design with a loop or a
parameter, or a closed statement that is false (it then falls back to the normalization and its goals),
behaves exactly as before.

**Many sites (WP-LIN).** On a design that is NOT flat (a parameter or a generate loop) the one-driver and rank
obligations were quadratic in the number of sites under `simp` as well (thousands of heartbeats at 11 / 21 / 41 plain sites:
one-driver 16 187 / 45 372 / 161 430, rank 35 726 / 112 829 / 403 666): `DisjObl` states `DisjOne` for EVERY pair of sites
and `RankObl'` filters ALL sites for the writers of every read, while only sites that write the SAME signal can fail
to be disjoint or ranked (two windows of different signals never overlap). The tactic therefore first restricts those two
obligations to the related sites (`groupStructureGoal`): it lists, natively and without `simp`, the pairs of sites that
write one signal (`sameNamePairs`) and, for every read, the writers of the signal it reads (`rdWriters`), assigns the
lemma of `CombViewGroup.lean` (`disjObl_of_groups`, `rankObl'_of_groups`: the original obligation asked on the listed
sites only, nesting kept) whose `rfl` hypothesis the kernel checks once, and hands THAT goal to the usual normalization.
The goals that come out are the same ones, in the same order, and no simp list gained a name; if the listing fails for
any reason, or the design has fewer than `groupMinSites` (four) sites, the original goal is normalized as before. `set_option sv_comb.profile true` logs the heartbeats each
obligation's normalization costs (thousands), the diagnostic these figures came from.

**The shared obligations (perf, 2026-11-04).** On the triple `CombDesign D ∧ Acyclic D ∧ SharedObl X.pdesign [N]`
(`CombShared.lean`) the tactic proves the bundle and packages the `auto` and `inRange` obligations it normalized anyway, so
that `sv_equations` can take them from the context instead of normalizing them a second time (`comb_acyclic_shared_view`,
`comb_lex_shared_view`; the obligations returned are those of the bundle).
-/

open Lean Elab Tactic Meta

open LeanModels.Sv.CombView

/-- `set_option sv_comb.profile true`: the sv_comb tactics log, per obligation, the heartbeats (in thousands) its
normalization costs (WP-LIN: a diagnostic for the cost of a design with many sites; off by default, no cost). -/
register_option sv_comb.profile : Bool := {
  defValue := false
  descr := "sv_comb tactics: log the heartbeats the normalization of each obligation costs" }

/-- Run the normalization of the obligation `nm`; with `sv_comb.profile` set, log what it cost. -/
def svObProfile (nm : String) (act : TacticM Unit) : TacticM Unit := do
  if sv_comb.profile.get (← getOptions) then
    let b ← IO.getNumHeartbeats
    act
    let a ← IO.getNumHeartbeats
    logInfo m!"sv_comb profile: {nm} {(a - b) / 1000}k heartbeats"
  else act

/-- `set_option sv_comb.group_report true`: the sv_comb tactics say, per obligation, how large the list of related sites is that
the grouped route restricted it to (WP-LIN: deterministic, so a test can pin it; a design that took the original route says
nothing). -/
register_option sv_comb.group_report : Bool := {
  defValue := false
  descr := "sv_comb tactics: report the size of the grouped list each obligation was restricted to" }

/-- Say `msg` when `sv_comb.group_report` is set. -/
def svGroupReport (msg : String) : Lean.Meta.MetaM Unit := do
  if sv_comb.group_report.get (← Lean.getOptions) then Lean.logInfo msg

unsafe def evalSummary (pd : Expr) : MetaM (Except String Summary) := do
  let ty := mkApp2 (mkConst ``Except [Level.zero, Level.zero]) (mkConst ``String)
    (mkConst ``LeanModels.Sv.CombView.Summary)
  evalExpr (Except String Summary) ty (mkApp (mkConst ``LeanModels.Sv.PDesign.summary) pd)


unsafe def evalArgs (e : Expr) : MetaM (List Int) :=
  evalExpr (List Int) (mkApp (mkConst ``List [Level.zero]) (mkConst ``Int)) e


unsafe def evalRank (e : Expr) : MetaM (SiteId → Nat) :=
  evalExpr (SiteId → Nat)
    (Lean.mkForall `x BinderInfo.default (mkConst ``LeanModels.Sv.CombView.SiteId) (mkConst ``Nat)) e

unsafe def evalLex (e : Expr) : MetaM (SiteId → Key) :=
  evalExpr (SiteId → Key)
    (Lean.mkForall `x BinderInfo.default (mkConst ``LeanModels.Sv.CombView.SiteId)
      (mkConst ``LeanModels.Sv.CombView.Key)) e


namespace LeanModels.Sv.CombView

/-- `X.sem N` is the alias-guarded family `PDesign.instantiateGDAlias2 X.pdesign [↑N]` (since ls-sv 7c9b7ac59;
before it, and in a goal stated at it, the unguarded `PDesign.instantiateGD2 X.pdesign [↑N]`): unfold until one of
them shows. The third component is `true` for the guarded family, which the tactics first rewrite to the unguarded
one the comb theorems are stated for (`aliasInertEq`). -/
partial def findGD2A (e : Lean.Expr) (fuel : Nat) : MetaM (Option (Lean.Expr × Lean.Expr × Bool)) := do
  let e ← whnfCore e
  if e.isAppOfArity ``LeanModels.Sv.PDesign.instantiateGDAlias2 2 then
    return some (e.getAppArgs[0]!, e.getAppArgs[1]!, true)
  if e.isAppOfArity ``LeanModels.Sv.PDesign.instantiateGD2 2 then
    return some (e.getAppArgs[0]!, e.getAppArgs[1]!, false)
  match fuel with
  | 0 => return none
  | fuel + 1 =>
    match ← unfoldDefinition? e with
    | some e' => findGD2A e' fuel
    | none => return none

/-- `X.sem N` of a design WITH module instances is `PDesign.instantiateHDAlias2 X.pdesign X.plib [↑N]`
(`PDesign.instantiateHD2` under the alias guard, `Hier2.lean`); the `sv_comb` tactics have no summary for it
(WP-I, step I0: say so instead of "cannot read a family"). -/
partial def isHD2Family (e : Lean.Expr) (fuel : Nat) : MetaM Bool := do
  let e ← whnfCore e
  if e.isAppOfArity `LeanModels.Sv.PDesign.instantiateHD2 3 ||
      e.isAppOfArity `LeanModels.Sv.PDesign.instantiateHDAlias2 3 then
    return true
  match fuel with
  | 0 => return false
  | fuel + 1 =>
    match ← unfoldDefinition? e with
    | some e' => isHD2Family e' fuel
    | none => return false

/-- The refusal of a design that instantiates modules. -/
def hierarchyRefusal (tac : String) : String :=
  s!"{tac}: this design instantiates modules, and the `sv_comb` tactics cannot summarize module instances yet. " ++
  "The loader, the scorer and the post-synthesis check accept such a design; the tactics do not. Flatten the design " ++
  "in the source (inline the instances into one module), or prove the structure by hand " ++
  "(`Examples/system-verilog/ripple_fa` is a worked by-hand proof of a hierarchical adder)"

/-! ### The exact 32-bit `int` reading of the parameters at a symbolic point (`hag`)

The instantiation binds an `int` parameter at `canonInt 32 true v` and an `int` localparam at its width-exact value
(`PDesign.paramEnv2`, `int32 := true`), while the summary's valuation `s.val args` is the unbounded integer. At
concrete arguments the two agree by `rfl`; at a symbolic one they agree where every value is in the signed 32-bit
range, which the tactics show from the hypotheses in context (`closeHag`). -/

theorem canonInt32_of_bounds {v : Int} (h1 : -2147483648 ≤ v) (h2 : v < 2147483648) :
    canonInt 32 true v = v :=
  canonInt32_of_range ⟨h1, h2⟩

/-- `hag` one name at a time (the head of the parameter list). -/
theorem hag_cons {f g : String → Option Int} {n : String} {ns : List String}
    (h : f n = g n) (t : ns.map f = ns.map g) : (n :: ns).map f = (n :: ns).map g := by
  rw [List.map_cons, List.map_cons, h, t]

/-- `$clog2` of a positive value is below it (`clog2 1 = 0`, and `clog2 n = log2 (n - 1) + 1 < n`): the fact that puts
`$clog2(N) + 1` in the 32-bit range wherever `N` is. The tactics hand it to `omega` with `clog2_le` for every `clog2`
of a range goal (`addClog2Facts`). -/
theorem clog2_zero_or_lt (n : Nat) : n = 0 ∨ LeanModels.Sv.clog2 n < n := by
  unfold LeanModels.Sv.clog2
  by_cases h : n ≤ 1
  · rw [if_pos h]; omega
  · rw [if_neg h]
    right
    have h2 : n - 1 ≠ 0 := by omega
    have := (Nat.log2_lt h2).2 (Nat.lt_two_pow_self (n := n - 1))
    omega

end LeanModels.Sv.CombView

/-- The free variables of an expression. -/
private partial def fvarsOf (e : Expr) : Array FVarId := Id.run do
  let mut acc : Array FVarId := #[]
  repeat
    match e.find? (fun x => x.isFVar && !acc.contains x.fvarId!) with
    | some x => acc := acc.push x.fvarId!
    | none => break
  return acc

/-- Lower bounds `c ≤ N` / `c < N` of the Nat variables of the arguments, from the context. -/
private def lowerBounds (fvs : Array FVarId) : MetaM Nat := do
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

/-- Name of a constant the summary was read from, to unfold it in the normalization. -/
private def headConst? (e : Expr) : Option Name :=
  match e.getAppFn with
  | .const n _ => some n
  | _ => none

-- COPY NOTE (literal simp list, kept in step by hand): `sv_norm_core` is one of six copies of the same
-- vocabulary: `sv_norm_core` (CombViewTactic.lean), `sv_eq_norm_at` and `sv_eq_norm` (CombEqTactic.lean),
-- `svL_norm_core`, `svL_eq_norm_at` and `svL_eq_norm` (CombProcTactic.lean). The L copies are the plain ones plus
-- the names of the procedural sites (skeletons, `NoSelfRead`, `EqsL`, ...); the `_at` copies act at a hypothesis,
-- the others at the goal. A lemma added to one list belongs in its siblings unless the difference is intended and
-- stated here. The multi-window copies `svL_eq_norm_multi_at` and `svL_eq_norm_multi` (CombProcTactic.lean) are
-- `svL_eq_norm_at` and `svL_eq_norm` plus the skeleton vocabulary; they name this note and each other.
/-- The normalization of the obligation `Prop`s: unfold the summary functions, evaluate the
affine forms, name the windows. -/
macro "sv_norm_core" : tactic =>
  `(tactic| (simp (config := { maxSteps := 4000000 }) only [LeanModels.Sv.CombView.Summary.AutoObl, LeanModels.Sv.CombView.Summary.lsites, LeanModels.Sv.CombView.Aff.add,
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

/-- `sv_norm [f, g]`: the normalization, with the player's own rank/key definitions `f`, `g`
unfolded. -/
syntax "sv_norm" ("[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

/-- The truncating `/` and `%` of a localparam's definition (`Int.tdiv`, `Int.tmod`: C semantics, what
the elaborated design computes) as the floor `/` and `%` that `omega` understands, where the
numerator is provably non-negative from the hypotheses in context (`hN : 1 ≤ N`). A numerator that
may be negative stays as `Int.tdiv`/`Int.tmod` in the goal (they really differ there). A no-op for a
design without localparams. -/
macro "sv_lp_norm" : tactic =>
  `(tactic| (try simp (disch := omega) only [Int.tdiv_eq_ediv_of_nonneg, Int.tmod_eq_emod_of_nonneg]))

/-- … on a hypothesis. -/
macro "sv_lp_norm_at" h:ident : tactic =>
  `(tactic| (try simp (disch := omega) only [Int.tdiv_eq_ediv_of_nonneg, Int.tmod_eq_emod_of_nonneg] at $h:ident))

macro_rules
  | `(tactic| sv_norm) => `(tactic| (sv_norm_core; sv_lp_norm; try sv_simp))
  | `(tactic| sv_norm [$ids,*]) =>
      `(tactic| (sv_norm_core; sv_lp_norm; (try simp (config := { maxSteps := 4000000 }) only [$ids,*]); try sv_simp))

/-- **Row-major bookkeeping, explicitly.** The 2-D windows of a packed array `x[R-1:0][W-1:0]` are
flat offsets `rmN W r c = r * W + c`, and every obligation about two of them (disjointness of two
cells, a cell inside a row or a part of a row, the overlap of a read with a write) is a comparison of
two such offsets. `sv_rowmajor` rewrites those comparisons into lexicographic comparisons of
`(row, column)` with the library lemmas `rmN_add_col` (a window's end is the offset of its end
column), `rmN_lt_iff` and `rmN_le_iff` (row-major order IS lexicographic order, for columns inside
the row); their side conditions (indices nonnegative, columns inside the row) are discharged by
`omega` from the loop bounds in the context. What it leaves is linear: finish with `omega`. It is
NOT part of `sv_structure`: the player calls it, on goals that mention `rmN`. -/
macro "sv_rowmajor" : tactic =>
  `(tactic| (try simp (disch := omega) only [LeanModels.Sv.CombView.rmN_add_col,
      LeanModels.Sv.CombView.rmN_lt_iff, LeanModels.Sv.CombView.rmN_le_iff] at *))

/-- **Close a decidable structural fact without an auxiliary lemma** (WP-P). `decide +kernel` turns the
fact into an auxiliary theorem and adds it to the environment synchronously, and in the asynchronous
elaboration of a file that addition waits for the kernel check of EVERY earlier declaration: the
`hok`/`hfrag` goals of a late theorem (`sv_interface`, `solution`) then sat idle for as long as the
heaviest earlier theorem took to elaborate (measured: 31 s of a 34 s `mul_wallace` interface theorem,
112 s of a 118 s `mul_tree` one, for a step that costs 0.3 s). Here the proposition is evaluated NATIVELY at
tactic time (`evalExpr` on `Decidable.decide`, milliseconds, with the tactic's own error when it is false),
and the goal is assigned `of_decide_eq_true _ _ (Eq.refl true)` directly: no environment change, so no
wait; the kernel evaluates the decision once, when it checks the enclosing theorem (the same work the
auxiliary lemma did, in the theorem's own asynchronous check). -/
unsafe def closeByDecide (g : MVarId) (what : String) : MetaM Unit := do
  let p ← instantiateMVars (← g.getType)
  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
  let d := mkApp2 (mkConst ``Decidable.decide) p inst
  let b ← evalExpr Bool (mkConst ``Bool) d
  unless b do throwError "{what}"
  g.assign (mkApp3 (mkConst ``of_decide_eq_true) p inst (← mkEqRefl (mkConst ``Bool.true)))

/-- **Deep recursion for the tactics' own work** (WP-P3b). A netlist of a hundred or more sites makes the
`simp` normalizations of the obligations recurse once per site (a right-nested conjunction of one fact
per site), and Lean's default `maxRecDepth` (512) stops them with `maximum recursion depth has been
reached` long before the work is large: the player had to write `set_option maxRecDepth 100000 in`
before the theorem. The tactics run their own steps with `maxRecDepth` raised to 100000 (the value
the references used), scoped to the tactic call through `Core.Context`: nothing in the player's file
changes, and a limit the player set higher is kept. -/
def withDeepRec {α : Type} (x : TacticM α) : TacticM α :=
  withTheReader Core.Context (fun c => { c with maxRecDepth := max c.maxRecDepth 100000 }) x


/-- **Decide the obligation of a flat netlist** (WP-P3b). `g` is an obligation goal (`s.DisjObl σ`,
`s.CoverObl σ`, …) of the summary `s`; `lem` is the `…_of_plain` lemma that reduces it to a closed, decidable
statement about the site list (`CombViewPlain.lean`, `CombEqPlain.lean`). When every site of `s` is plain and
the goal mentions no free variable or metavariable (no parameter), the lemma is applied and its premises are
closed with `closeByDecide`; the result is `true` and `g` is closed. Anything else, including a premise that is
false, restores the state and returns `false`: the caller takes the normalization route, unchanged. -/
unsafe def tryClosePlain (s : LeanModels.Sv.CombView.Summary) (g : MVarId) (lem : Name) (what : String) :
    TacticM Bool := do
  unless s.lsites.all fun ls => ls.hdrs.isEmpty do return false
  let ty ← instantiateMVars (← g.getType)
  if ty.hasFVar || ty.hasExprMVar then return false
  let saved ← saveState
  try
    let gs ← g.apply (← mkConstWithFreshMVarLevels lem)
    for g' in gs do closeByDecide g' what
    setGoals []
    return true
  catch _ =>
    saved.restore
    return false

/-- The elements of a list expression, by weak head normalization of its spine (WP-LIN). -/
partial def listElemExprs (e : Expr) : MetaM (Array Expr) := do
  let mut acc : Array Expr := #[]
  let mut cur ← whnf e
  repeat
    match cur.getAppFnArgs with
    | (``List.cons, #[_, x, xs]) =>
        acc := acc.push (← instantiateMVars x).headBeta
        cur ← whnf xs
    | (``List.nil, _) => break
    | _ => throwError "sv_comb: cannot read a list expression element by element"
  return acc

namespace LeanModels.Sv.CombView

/-- **The alias guard, out of the way** (ls-sv 7c9b7ac59): the equation `D = pd.instantiateGD2 args` for the design
`D` of the goal, which unfolds to the guarded family `pd.instantiateGDAlias2 args`. The static check
`PDesign.aliasInert pd` (`CombAliasInert.lean`) is decided natively and by the kernel (`closeByDecide`); a design with
an `always_comb` beside a continuous assignment fails it, and the tactic `tac` refuses the design, saying why. -/
unsafe def aliasInertEq (tac : String) (D pd args : Lean.Expr) : MetaM Lean.Expr := do
  let hqTy ← mkEq (mkApp (mkConst ``LeanModels.Sv.PDesign.aliasInert) pd) (mkConst ``Bool.true)
  let hq ← mkFreshExprMVar hqTy
  try closeByDecide hq.mvarId! "not inert"
  catch _ =>
    throwError "{tac}: the design family applies the `always_comb` alias guard (`X.sem N` is `PDesign.instantiateGDAlias2`, `CombAlias2.lean`), and the comb theorems are stated for the unguarded family `PDesign.instantiateGD2`. Without a lowering in hand the tactics show that the guard keeps every process only for a design with no `always_comb` or with no continuous `assign` (`PDesign.aliasInert`, `CombAliasInert.lean`); this design has both (the `always_comb` form of `sv_structure` shows the guard inert from the summary's names, `Summary.aliasOk`, `CombProcAlias.lean`; where `hl : (X.sem N).lowerComb = some d'` is in context, `sv_interface` and `sv_equations` read the guard off it)"
  let D' := mkApp2 (mkConst ``LeanModels.Sv.PDesign.instantiateGD2) pd args
  let pf := mkApp3 (mkConst ``LeanModels.Sv.PDesign.instantiateGDAlias2_of_aliasInert) pd
    (← instantiateMVars hq) args
  mkExpectedTypeHint pf (← mkEq D D')

/-- The equation `D = pd.instantiateGD2 args` from `hl : D.lowerComb = some d'`, for `D` the guarded family
`pd.instantiateGDAlias2 args`: a guarded design that lowers is its own guard
(`PDesign.instantiateGDAlias2_of_lowerComb`); no static check, every design. -/
def aliasLowerEq (D pd args hl : Lean.Expr) : MetaM Lean.Expr := do
  let some (_, _, rhs) := (← instantiateMVars (← inferType hl)).eq?
    | throwError "sv_comb: internal error: the lowering hypothesis is not an equation"
  unless rhs.isAppOfArity ``Option.some 2 do
    throwError "sv_comb: internal error: the lowering hypothesis is not `… = some d'`"
  let pf := mkAppN (mkConst ``LeanModels.Sv.PDesign.instantiateGDAlias2_of_lowerComb) #[pd, args, rhs.appArg!, hl]
  mkExpectedTypeHint pf (← mkEq D (mkApp2 (mkConst ``LeanModels.Sv.PDesign.instantiateGD2) pd args))

/-- Replace the design `D` by `D'` in the target of `g` along `hA : D = D'` (every occurrence). -/
def rewriteDesign (g : MVarId) (hA : Lean.Expr) : MetaM MVarId := do
  let r ← g.rewrite (← instantiateMVars (← g.getType)) hA
  unless r.mvarIds.isEmpty do throwError "sv_comb: internal error: the design rewrite left goals"
  g.replaceTargetEq r.eNew r.eqProof

/-- A hypothesis `h : T[D]` as a proof of `T[D']`, along `hA : D = D'` (unchanged when `T` does not mention `D`). -/
def transportDesign (h D hA : Lean.Expr) : MetaM Lean.Expr := do
  let T ← instantiateMVars (← inferType h)
  let Tabs ← kabstract T D
  unless Tabs.hasLooseBVars do return h
  let some (_, _, D') := (← instantiateMVars (← inferType hA)).eq?
    | throwError "sv_comb: internal error: the design equation is not an equation"
  let motive := Lean.mkLambda `x .default (← inferType D) Tabs
  let eq ← mkCongrArg motive hA
  mkExpectedTypeHint (← mkEqMP eq h) (Tabs.instantiate1 D')

/-- The summary's valuation of a localparam definition as a term over the terms `m` of the names before it
(`CE.eval`, operation for operation), so that it is definitionally `s.val args n`. -/
partial def ceTerm (m : List (String × Lean.Expr)) : CE → MetaM Lean.Expr
  | .lit v => pure (toExpr v)
  | .ref n => pure ((m.lookup n).getD (toExpr (0 : Int)))
  | .add a b => do mkAppM ``HAdd.hAdd #[← ceTerm m a, ← ceTerm m b]
  | .sub a b => do mkAppM ``HSub.hSub #[← ceTerm m a, ← ceTerm m b]
  | .mul a b => do mkAppM ``HMul.hMul #[← ceTerm m a, ← ceTerm m b]
  | .divK a k => do mkAppM ``Int.tdiv #[← ceTerm m a, toExpr k]
  | .modK a k => do mkAppM ``Int.tmod #[← ceTerm m a, toExpr k]
  | .clog2 a => do
      let n ← mkAppM ``LeanModels.Sv.clog2 #[← mkAppM ``Int.toNat #[← ceTerm m a]]
      mkAppOptM ``Nat.cast #[mkConst ``Int, none, n]
  | .clog2S a => do
      let n ← mkAppM ``LeanModels.Sv.clog2 #[← mkAppM ``Int.toNat #[← ceTerm m a]]
      let c ← mkAppOptM ``Nat.cast #[mkConst ``Int, none, n]
      pure (mkApp3 (mkConst ``LeanModels.Sv.canonInt) (toExpr (32 : Nat)) (toExpr true) c)

/-- The arguments `a` of the `clog2 a` subterms of `e` (closed under no binder). -/
partial def clog2Args (e : Lean.Expr) : Array Lean.Expr :=
  match e with
  | .app f a =>
      (if e.isAppOfArity ``LeanModels.Sv.clog2 1 && !a.hasLooseBVars then #[a] else #[]) ++ clog2Args f ++
        clog2Args a
  | .lam _ t b _ | .forallE _ t b _ => clog2Args t ++ clog2Args b
  | .letE _ t v b _ => clog2Args t ++ clog2Args v ++ clog2Args b
  | .mdata _ b | .proj _ _ b => clog2Args b
  | _ => #[]

/-- `a` and the forms the tactics' `simp` sets give it (`Int.ofNat n` as `↑n`, then `(↑n).toNat` as `n`): `omega` reads
`clog2 a` as an atom up to syntax, so a fact is stated for each. -/
def clog2Variants (a : Lean.Expr) : Array Lean.Expr :=
  let cast (x : Lean.Expr) : Lean.Expr :=
    mkApp3 (mkConst ``Nat.cast [Level.zero]) (mkConst ``Int) (mkConst ``instNatCastInt) x
  let a1 := a.replace fun x => if x.isAppOfArity ``Int.ofNat 1 then some (cast x.appArg!) else none
  let a2 := a1.replace fun x =>
    if x.isAppOfArity ``Int.toNat 1 && x.appArg!.isAppOfArity ``Nat.cast 3 then some x.appArg!.appArg! else none
  #[a, a1, a2]

/-- Put `clog2_le a` and `clog2_zero_or_lt a` in the context of the main goal for every `clog2 a` of the terms `es`, for
`omega` (which reads `clog2 a` as an atom). -/
def addClog2Facts (es : Array Lean.Expr) : TacticM Unit := do
  let mut seen : Array Lean.Expr := #[]
  for e in es do
    for a in (clog2Args (← instantiateMVars e)).flatMap clog2Variants do
      if seen.contains a then continue
      seen := seen.push a
      let g ← getMainGoal
      let h1 := mkApp (mkConst ``LeanModels.Sv.CombView.clog2_le) a
      let h2 := mkApp (mkConst ``LeanModels.Sv.CombView.clog2_zero_or_lt) a
      let g ← g.assert `hclog2_le (← inferType h1) h1
      let (_, g) ← g.intro1P
      let g ← g.assert `hclog2_lt (← inferType h2) h2
      let (_, g) ← g.intro1P
      replaceMainGoal [g]

/-- **Close `hag`** (`s.params.map (fun n => env.intVal? n) = s.params.map (fun n => some (s.val args n))`), the
agreement of the instantiation environment with the summary's valuation. At concrete arguments `rfl` decides it. At
a symbolic argument the environment holds each `int` parameter and localparam at its exact 32-bit value, `canonInt 32
true` of the argument or of the width-exact fold of the definition, and the valuation holds the unbounded integer:
for each name the tactic reads the environment's value (by unification, the computation `rfl` did), states it against
the valuation's value, and removes every `canonInt 32 true` whose argument `omega` shows to be in the signed 32-bit
range from the hypotheses in context (`canonInt32_of_bounds`, with `Int.tdiv`/`Int.tmod` of a non-negative numerator
as `/`/`%`). A value it cannot place in range is an error that names it: a theorem at a symbolic `int` parameter
needs its range premise, e.g. `(hR : (N : Int) < 2147483648)`. -/
unsafe def closeHag (tac : String) (g : MVarId) (sv : Summary) (args : Lean.Expr) : TacticM Unit := do
  let what := "the parameter values could not be read off the instantiation environment"
  let argsI ← instantiateMVars args
  if !argsI.hasFVar && !argsI.hasMVar then
    setGoals [g]
    try evalTactic (← `(tactic| rfl)) catch e => throwError "{tac}: {what}\n{e.toMessageData}"
    unless (← getGoals).isEmpty do throwError "{tac}: {what}"
    return
  g.withContext do
    let ty ← instantiateMVars (← g.getType)
    let some (_, lhs, rhs) := ty.eq? | throwError "{tac}: internal error: `hag` is not an equation"
    unless lhs.isAppOfArity ``List.map 4 && rhs.isAppOfArity ``List.map 4 do
      throwError "{tac}: internal error: `hag` is not an equation of two maps"
    let f := lhs.getAppArgs[2]!
    let gf := rhs.getAppArgs[2]!
    let argEs ← listElemExprs argsI
    let mut m : List (String × Lean.Expr) := (sv.params.zip argEs.toList).reverse
    for (n, c) in sv.lps do
      m := (n, ← ceTerm m c) :: m
    let strT := mkConst ``String
    let mut acc : Lean.Expr ← mkExpectedTypeHint
      (← mkEqRefl (mkApp4 (mkConst ``List.map [Level.zero, Level.zero]) strT
        (mkApp (mkConst ``Option [Level.zero]) (mkConst ``Int)) f (mkApp (mkConst ``List.nil [Level.zero]) strT)))
      (← mkEq (mkApp4 (mkConst ``List.map [Level.zero, Level.zero]) strT
          (mkApp (mkConst ``Option [Level.zero]) (mkConst ``Int)) f (mkApp (mkConst ``List.nil [Level.zero]) strT))
        (mkApp4 (mkConst ``List.map [Level.zero, Level.zero]) strT
          (mkApp (mkConst ``Option [Level.zero]) (mkConst ``Int)) gf (mkApp (mkConst ``List.nil [Level.zero]) strT)))
    let mut suffix : List String := []
    for n in sv.params.reverse do
      let nE := toExpr n
      let v ← mkFreshExprMVar (mkConst ``Int)
      unless ← isDefEq (mkApp f nE).headBeta (← mkAppM ``Option.some #[v]) do
        throwError "{tac}: {what}: `{n}` is not bound as a 32-bit signed `int` in the instantiation environment"
      let v ← instantiateMVars v
      let r := (m.lookup n).getD (toExpr (0 : Int))
      unless ← isDefEq (mkApp gf nE).headBeta (← mkAppM ``Option.some #[r]) do
        throwError "{tac}: internal error: the valuation of `{n}` is not `{r}`"
      let pg ← mkFreshExprSyntheticOpaqueMVar (← mkEq (← mkAppM ``Option.some #[v]) (← mkAppM ``Option.some #[r]))
      setGoals [pg.mvarId!]
      addClog2Facts #[v, r]
      try
        evalTactic (← `(tactic| ((try simp (disch := omega) only [Int.ofNat_eq_natCast,
            LeanModels.Sv.CombView.canonInt32_of_bounds, Int.tdiv_eq_ediv_of_nonneg, Int.tmod_eq_emod_of_nonneg,
            Option.some.injEq]) <;> first | rfl | omega)))
      catch _ =>
        throwError "{tac}: {what}: at a symbolic parameter the instantiation holds `{n}` at its exact 32-bit `int` value `{v}`, which is the summary's `{r}` only where every value is in the signed 32-bit range [-2147483648, 2147483647], and `omega` could not show that from the hypotheses in context (a theorem at a symbolic `int` parameter needs a range premise such as `(hR : (N : Int) < 2147483648)`)"
      unless (← getGoals).isEmpty do throwError "{tac}: {what} (`{n}`)"
      let h ← mkExpectedTypeHint (← instantiateMVars pg) (← mkEq (mkApp f nE) (mkApp gf nE))
      acc := mkAppN (mkConst ``LeanModels.Sv.CombView.hag_cons) #[f, gf, nE, toExpr suffix, h, acc]
      suffix := n :: suffix
    unless ← isDefEq ty (← inferType acc) do
      throwError "{tac}: internal error: the parameter list is not `{sv.params}`"
    g.assign acc
    setGoals []

/-! ### The parameter stage at a symbolic point (`h1`)

`h1 : pd.paramEnv2 args = .ok ?env` is the instantiation environment, computed by `rfl`. At a symbolic `int`
argument the computation carries `canonInt 32 true v`, the exact 32-bit value, and it stops wherever it DECIDES on such a
value: the sign test of `$clog2` (`$clog2` of a negative value is an error), and any fold after it. `closeParamEnv`
first tries `rfl`; where `rfl` is stuck it evaluates the left-hand side with `canonInt` held back
(`whnfCanon`) down to the first `canonInt 32 true x` the evaluation needs (`exposeCanon`: the term is reduced only along
the path to it, so it is definitionally the goal's), shows `x` in the signed 32-bit range from the hypotheses in context
(`omega`, with `Int.tdiv`/`Int.tmod` of a non-negative numerator as `/`/`%` and the `clog2` facts), rewrites
`canonInt 32 true x` to `x` (`canonInt32_of_bounds`) and tries `rfl` again. Every rewrite is a kernel-checked equation;
the environment the final `rfl` computes holds the values in range, as the summary does. A value it cannot place in
range is an error that names it. -/

/-- `whnf` with `canonInt` held back. -/
def whnfCanon (e : Lean.Expr) : MetaM Lean.Expr :=
  withCanUnfoldPred (fun _ ci => pure (ci.name != ``LeanModels.Sv.canonInt)) (whnf e)

/-- **The first `canonInt` an evaluation needs**: `e` reduced along the path to the first stuck application
`t = canonInt w s x` with `x` mentioning a free variable (the innermost one first), definitionally `e`, with `t` a
syntactic subterm; subterms that already contain `t` are kept unreduced. `none`: no such application. -/
partial def exposeCanon (e : Lean.Expr) (fuel : Nat) : MetaM (Option (Lean.Expr × Lean.Expr)) := do
  if fuel == 0 || !e.hasFVar then return none
  let e' ← whnfCanon e
  let found? : Option (Lean.Expr × Lean.Expr) ← do
    if e'.isAppOfArity ``LeanModels.Sv.canonInt 3 then
      let x := e'.appArg!
      match ← exposeCanon x (fuel - 1) with
      | some (x', t) =>
          pure (some (mkApp e'.appFn! (if (x.find? (· == t)).isSome then x else x'), t))
      | none => pure (if x.hasFVar then some (e', e') else none)
    else if e'.isApp then
      let fn := e'.getAppFn
      let args := e'.getAppArgs
      let mut res : Option (Lean.Expr × Lean.Expr) := none
      for i in [0:args.size] do
        let a := args[i]!
        if a.isLambda || a.isSort || a.hasLooseBVars then continue
        if (← isType a) || (← isProof a) then continue
        if let some (a', t) ← exposeCanon a (fuel - 1) then
          res := some (mkAppN fn (args.set! i (if (a.find? (· == t)).isSome then a else a')), t)
          break
      pure res
    else if let .proj sn i b := e' then
      -- a projection of a stuck structure (`Decidable.decide` of a stuck instance)
      match ← exposeCanon b (fuel - 1) with
      | some (b', t) => pure (some (.proj sn i (if (b.find? (· == t)).isSome then b else b'), t))
      | none => pure none
    else pure none
  match found? with
  | some (e'', t) => return some (if (e.find? (· == t)).isSome then e else e'', t)
  | none => return none

/-- **Close `h1`** (`pd.paramEnv2 args = .ok ?env`): `rfl`, or, where the computation stops at an exact 32-bit
value, the rewrites described above, then `rfl`. -/
unsafe def closeParamEnv (tac : String) (g : MVarId) : TacticM Unit := do
  let what := "the parameter stage (`paramEnv2`) of this design could not be evaluated at a symbolic parameter"
  let tryRfl (g : MVarId) : TacticM Bool := do
    let st ← saveState
    setGoals [g]
    try
      evalTactic (← `(tactic| rfl))
      if (← getGoals).isEmpty then return true
      st.restore; return false
    catch _ =>
      st.restore; return false
  if ← tryRfl g then return
  let mut g := g
  for _ in [0:32] do
    let some (gN, t, x) ← g.withContext do
        let ty ← instantiateMVars (← g.getType)
        let some (_, lhs, rhs) := ty.eq? | throwError "{tac}: internal error: `h1` is not an equation"
        let some (lhs', t) ← exposeCanon lhs 400 | return none
        let x := t.appArg!
        let ws := t.appFn!.appFn!.appArg!
        let sg := t.appFn!.appArg!
        unless (← isDefEq ws (toExpr (32 : Nat))) && (← isDefEq sg (toExpr true)) do
          throwError "{tac}: {what}: the instantiation evaluates `{t}` at a symbolic parameter (only the 32-bit signed reading, `canonInt 32 true`, is placed in range)"
        let g1 ← g.replaceTargetDefEq (← mkEq lhs' rhs)
        pure (some (g1, t, x))
      | throwError "{tac}: {what}"
    -- `x` in the signed 32-bit range, from the hypotheses in context (the hypotheses of `canonInt32_of_bounds`)
    let pfFn := mkApp (mkConst ``LeanModels.Sv.CombView.canonInt32_of_bounds) x
    let (bs, _, _) ← gN.withContext do forallMetaTelescopeReducing (← inferType pfFn)
    for b in bs do
      setGoals [b.mvarId!]
      addClog2Facts #[x]
      try
        evalTactic (← `(tactic| ((try simp (disch := omega) only [Int.ofNat_eq_natCast, Int.toNat_natCast,
            Int.tdiv_eq_ediv_of_nonneg, Int.tmod_eq_emod_of_nonneg]) <;> omega)))
      catch _ =>
        throwError "{tac}: {what}: the instantiation decides on `{t}`, the exact 32-bit `int` value of `{x}`, which is `{x}` only in the signed 32-bit range [-2147483648, 2147483647], and `omega` could not show that from the hypotheses in context (a theorem at a symbolic `int` parameter needs a range premise such as `(hR : (N : Int) < 2147483648)`, and a derived value one of its own)"
      unless (← getGoals).isEmpty do throwError "{tac}: {what} (`{x}` in range)"
    let eq ← instantiateMVars (mkAppN pfFn bs)
    g ← gN.withContext do rewriteDesign gN eq
    if ← tryRfl g then return
  throwError "{tac}: {what}"

end LeanModels.Sv.CombView

/-- **Below this many sites the grouped route is not taken** (WP-LIN). Listing the related sites costs a weak head
normalization of the site list and of each site's reads, a fixed price that the avoided pairs only repay from a few sites on:
measured, a design of ONE site (`prio_enc`, the 256-entry `sbox_table`) pays 1.6 to 4.4 million heartbeats for nothing, and a
flat chain of five sites already saves 14% of its structure cost. Smaller designs are normalized as before. -/
def groupMinSites : Nat := 4

/-- **`rdWriters s.lsites` as an expression, with the proof of `rdWriters s.lsites = RW`** (WP-LIN, `CombViewGroup.lean`).
`sv` is the value of the summary, `sE` its expression: the tactic lists, natively and without `simp`, every site with its
reads and, for each read, the writers of the signal it reads; the sites and reads are the terms the weak head normal form of
`s.lsites` gives (so the kernel's `rfl` check of the equation is a comparison of the names). The rank and the coverage
obligations are stated over this list. -/
def rdWritersExpr (sv : LeanModels.Sv.CombView.Summary) (sE : Expr) : MetaM (Expr × Expr × Nat × Nat) := do
  let lsT := mkConst ``LeanModels.Sv.CombView.LSite
  let accT := mkConst ``LeanModels.Sv.CombView.Acc
  let listOf (t : Expr) := mkApp (mkConst ``List [Level.zero]) t
  let prodT (a b : Expr) := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) a b
  let prodMk (α β a b : Expr) := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) α β a b
  let names := sv.lsites.toArray.map fun l => l.site.tgt.name
  let rdNamesAll := sv.lsites.toArray.map fun l => l.site.rds.toArray.map fun r => r.name
  let n := names.size
  let sites ← listElemExprs (mkApp (mkConst ``LeanModels.Sv.CombView.Summary.lsites) sE)
  unless sites.size == n do throwError "sv_comb: the site list differs from the summary's"
  let rdT := prodT accT (listOf lsT)
  let eT := prodT lsT (listOf rdT)
  let mut entries : Array Expr := #[]
  let mut nReads := 0
  let mut nWriters := 0
  for i in [0:n] do
    let rs ← listElemExprs (mkApp (mkConst ``LeanModels.Sv.CombView.TSite.rds)
      (mkApp (mkConst ``LeanModels.Sv.CombView.LSite.site) sites[i]!))
    let rdNames := rdNamesAll[i]!
    unless rs.size == rdNames.size do throwError "sv_comb: the read list differs from the summary's"
    let mut qs : Array Expr := #[]
    for k in [0:rs.size] do
      let mut ws : Array Expr := #[]
      for j in [0:n] do
        if names[j]! == rdNames[k]! then ws := ws.push sites[j]!
      nReads := nReads + 1
      nWriters := nWriters + ws.size
      qs := qs.push (prodMk accT (listOf lsT) rs[k]! (← mkListLit lsT ws.toList))
    entries := entries.push (prodMk lsT (listOf rdT) sites[i]! (← mkListLit rdT qs.toList))
  let RW ← mkListLit eT entries.toList
  let hRW := mkApp2 (mkConst ``Eq.refl [Level.one]) (listOf eT) RW
  return (RW, hRW, nReads, nWriters)

/-- **The grouped route for the two quadratic structure obligations** (WP-LIN, `CombViewGroup.lean`). `g` is the goal
`s.DisjObl σ` or `s.RankObl ρ σ` / `s.LexObl κ σ` of the summary `s` (a closed term, evaluated as the value `sv`). Only
the pairs of sites that write the SAME signal, and the triples (site, read, writer of the signal read), can fail to hold
trivially; the tactic lists them natively (from the target names, no `simp`), assigns the lemma of `CombViewGroup` whose
`rfl` hypothesis the kernel checks once, and returns the new goal: the original obligation restricted to that list,
which the usual normalization then handles in time linear in the number of listed pairs. -/
def groupStructureGoal (sv : LeanModels.Sv.CombView.Summary) (g : MVarId) : MetaM MVarId := do
  let ty ← instantiateMVars (← g.getType)
  let lsT := mkConst ``LeanModels.Sv.CombView.LSite
  let prodT (a b : Expr) := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) a b
  let prodMk (a b : Expr) (α β : Expr) := mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) α β a b
  let names := sv.lsites.toArray.map fun l => l.site.tgt.name
  let n := names.size
  if ty.isAppOfArity ``LeanModels.Sv.CombView.Summary.DisjObl 2 then
    let sE := ty.appFn!.appArg!
    let σE := ty.appArg!
    let sites ← listElemExprs (mkApp (mkConst ``LeanModels.Sv.CombView.Summary.lsites) sE)
    unless sites.size == n do throwError "sv_structure: the site list differs from the summary's"
    let mut pairs : Array Expr := #[]
    for i in [0:n] do
      for j in [i+1:n] do
        if names[i]! == names[j]! then pairs := pairs.push (prodMk sites[i]! sites[j]! lsT lsT)
    let pT := prodT lsT lsT
    svGroupReport s!"sv_comb group: DisjObl, {pairs.size} same-signal pairs of {n} sites"
    let P ← mkListLit pT pairs.toList
    let listT := mkApp (mkConst ``List [Level.zero]) pT
    let hP := mkApp2 (mkConst ``Eq.refl [Level.one]) listT P
    let app := mkApp4 (mkConst ``LeanModels.Sv.CombView.Summary.disjObl_of_groups) sE σE P hP
    let hTy := (← whnf (← inferType app)).bindingDomain!
    let hNew ← mkFreshExprSyntheticOpaqueMVar hTy (← g.getTag)
    g.assign (mkApp app hNew)
    return hNew.mvarId!
  else
    -- `RankObl ρ σ` and `LexObl κ σ` unfold to `RankObl' R σ`
    let ty' ← match ← unfoldDefinition? ty with
      | some t => pure t.headBeta
      | none => pure ty
    unless ty'.isAppOfArity ``LeanModels.Sv.CombView.Summary.RankObl' 3 do
      throwError "sv_structure: not a rank obligation"
    let sE := ty'.appFn!.appFn!.appArg!
    let RE := ty'.appFn!.appArg!
    let σE := ty'.appArg!
    let (RW, hRW, nReads, nWriters) ← rdWritersExpr sv sE
    svGroupReport s!"sv_comb group: RankObl', {nReads} reads with {nWriters} writers of {n} sites"
    let app := mkApp5 (mkConst ``LeanModels.Sv.CombView.Summary.rankObl'_of_groups) sE RE σE RW hRW
    let hTy := (← whnf (← inferType app)).bindingDomain!
    let hNew ← mkFreshExprSyntheticOpaqueMVar hTy (← g.getTag)
    g.assign (mkApp app hNew)
    return hNew.mvarId!

/-- The simp lemmas that unfold the REPLICATION vocabulary (WP-B2 gate 4c: the counts of a site, `repAff`, the affine
reader behind it). They are passed to `simp` ONLY for a design that contains a replication (`Summary.hasRepl`), never named
in the tactics' own lists: a name in those lists costs about 21 units of heartbeats per `simp` call, on every proof. -/
def replSimpLemmas {m : Type → Type} [Monad m] [MonadQuotation m] :
    m (Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) := do
  return #[← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.PExpr.rcounts),
    ← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.PExpr.consts),
    ← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.CombView.repCount),
    ← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.CombView.repAff),
    ← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.CombView.affOf?),
    ← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.CombView.affBin),
    ← `(Lean.Parser.Tactic.simpLemma| LeanModels.Sv.CombView.affMul),
    ← `(Lean.Parser.Tactic.simpLemma| List.isEmpty_nil),
    ← `(Lean.Parser.Tactic.simpLemma| List.isEmpty_cons)]

/-- `t` (a normalization step `at h`), preceded by the replication vocabulary when the design has a replication. -/
def withRepl {m : Type → Type} [Monad m] [MonadQuotation m] (hasRepl : Bool)
    (replL : Array (TSyntax ``Lean.Parser.Tactic.simpLemma)) (h : Ident) (t : TSyntax `tactic) :
    m (TSyntax `tactic) :=
  if hasRepl then
    `(tactic| first | (simp only [$replL,*] at $h:ident; try $t:tactic) | $t:tactic)
  else pure t

/-- Run the structural stage. (`unsafe`: it evaluates the recognizer on the design with
`evalExpr`, at tactic time only.) -/
unsafe def runSvStructure (rankStx? lexStx? usingStx? : Option Syntax) (hintOnly : Bool) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    -- the bundle `CombDesign D ∧ Acyclic D` (WP-P): one application of `Summary.sound`, one round of
    -- obligations for both
    -- the triple `CombDesign D ∧ Acyclic D ∧ SharedObl X.pdesign args` (perf, CombShared.lean): the bundle, and the
    -- `auto`/`inRange` obligations packaged for `sv_equations`
    let isShared := ty.isAppOfArity ``And 2 &&
      ty.appFn!.appArg!.getAppFn.isConstOf ``LeanModels.Sv.CombDesign &&
      ty.appArg!.isAppOfArity ``And 2 &&
      ty.appArg!.appFn!.appArg!.getAppFn.isConstOf ``LeanModels.Sv.Acyclic &&
      ty.appArg!.appArg!.getAppFn.isConstOf ``LeanModels.Sv.CombView.SharedObl
    let isBoth := isShared || (ty.isAppOfArity ``And 2 &&
      ty.appFn!.appArg!.getAppFn.isConstOf ``LeanModels.Sv.CombDesign &&
      ty.appArg!.getAppFn.isConstOf ``LeanModels.Sv.Acyclic)
    let isComb := ty.getAppFn.isConstOf ``LeanModels.Sv.CombDesign
    let isAcyc := ty.getAppFn.isConstOf ``LeanModels.Sv.Acyclic || isBoth
    unless isComb || isAcyc do
      throwError "sv_structure: the goal must be `CombDesign (X.sem N)`, `Acyclic (X.sem N)`, their conjunction `CombDesign (X.sem N) ∧ Acyclic (X.sem N)`, or that conjunction with the shared obligations `∧ SharedObl X.pdesign [N]` (for `sv_equations`)"
    let dGoal := if isBoth then ty.appFn!.appArg!.appArg! else ty.appArg!
    let some (pd, args, aliased) ← findGD2A dGoal 8
      | if (← isHD2Family dGoal 8) then throwError (hierarchyRefusal "sv_structure")
        else throwError "sv_structure: cannot read a `load_design_sv2` family (`X.sem N`) off the design in the goal"
    let some pdName := headConst? pd
      | throwError "sv_structure: the design is not a named constant"
    match ← evalSummary pd with
    | .error msg =>
        throwError "sv_structure: outside the supported fragment — {msg}"
    | .ok s =>
      if hintOnly then
        logInfo m!"{s.describe}"
        return
      -- structural facts, with the specific reason when one fails
      let probs := s.structProblems
      unless probs.isEmpty do
        throwError "sv_structure: structural check failed:\n  {"\n  ".intercalate probs}"
      -- the Nat variables of the arguments, and small sample values for them
      let fvs ← (fvarsOf args).filterM fun f => do
        return (← f.getType).isConstOf ``Nat
      let lb ← lowerBounds fvs
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
      if usingStx?.isSome && !isAcyc then
        throwError "sv_structure: `using hc` is for an `Acyclic` goal (it supplies the one-driver obligation from `CombDesign`)"
      if usingStx?.isSome && isBoth then
        throwError "sv_structure: `using hc` is for an `Acyclic` goal alone; the conjunction `CombDesign ∧ Acyclic` derives the one-driver obligation itself"
      if isAcyc && rankE?.isNone && lexE?.isNone then
        throwError "sv_structure: an `Acyclic` goal needs a rank over site identities, e.g. `sv_structure (rank := rippleRank … …)` or a lexicographic key `sv_structure (lexRank := fun | .plain 0 => (0, 0, 0) | …)`; run `sv_structure?` to see the sites and the rank relation they must satisfy"
      -- sampling: genuine violations are reported with the offending sites
      for k in [lb, lb + 1, lb + 2, lb + 3, lb + 4] do
        let lits := fvs.map fun _ => (mkNatLit k)
        let argsK := args.replaceFVars (fvs.map mkFVar) lits
        let argVals ← evalArgs argsK
        let σ := s.val argVals
        let ctxMsg := s!"(sampled at {s.pnames} = {argVals}; a genuine violation, not a missing proof, unless your hypotheses exclude this point)"
        if let some m := s.accCounterexample σ then
          throwError "sv_structure: in-range obligation fails — {m} {ctxMsg}"
        if let some m := s.rangeCounterexample σ then
          throwError "sv_structure: in-range obligation fails — {m} {ctxMsg}"
        if let some m := s.disjCounterexample σ then
          throwError "sv_structure: {m} {ctxMsg}"
        if let some re := rankE? then
          let reK := re.replaceFVars (fvs.map mkFVar) lits
          let ρ ← evalRank reK
          if let some m := s.rankCounterexample σ (fun w r => decide (ρ w < ρ r))
              (fun i => toString (ρ i)) then
            throwError "sv_structure: {m} {ctxMsg}{(s.rankReadNote σ (fun w r => decide (ρ w < ρ r))).getD ""}"
        if let some le := lexE? then
          let leK := le.replaceFVars (fvs.map mkFVar) lits
          let κ ← evalLex leK
          if let some m := s.rankCounterexample σ (fun w r => decide (KLt (κ w) (κ r)))
              (fun i => showKey (κ i)) then
            throwError "sv_structure: {m} {ctxMsg}{(s.rankReadNote σ (fun w r => decide (KLt (κ w) (κ r)))).getD ""}"
      -- the proof
      -- the alias-guarded family (`X.sem N`, ls-sv 7c9b7ac59): the goal is restated at the unguarded family the
      -- theorems are about, along `X.sem N = X.pdesign.instantiateGD2 [N]` (`aliasInertEq`), and so is `using hc`
      let mut usingStx? := usingStx?
      if aliased then
        let hA ← aliasInertEq "sv_structure" dGoal pd args
        replaceMainGoal [← rewriteDesign (← getMainGoal) hA]
        if let some u := usingStx? then
          let hcE ← Tactic.elabTerm u none
          usingStx? := some (← Term.exprToSyntax (← transportDesign hcE dGoal hA)).raw
      let pdId := mkIdent pdName
      let replL ← if s.hasRepl then replSimpLemmas else pure #[]
      let pdL ← `(Lean.Parser.Tactic.simpLemma| $pdId:ident)
      let preL : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) := #[pdL] ++ replL
      -- the player's own rank/key function, if it is a named definition: unfold it
      let keyIds : Array Ident :=
        match (rankE?.orElse fun _ => lexE?) with
        | some e =>
            match e.getAppFn with
            | .const n _ => #[mkIdent n]
            | _ => #[]
        | none => #[]
      let keyLemmas ← keyIds.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
      let normR : TSyntax `tactic ←
        if s.hasRepl then `(tactic| (sv_norm [$keyLemmas,*]; (try simp only [$replL,*]); try sv_norm [$keyLemmas,*]))
        else `(tactic| sv_norm [$keyLemmas,*])
      if isComb then
        evalTactic (← `(tactic|
          refine LeanModels.Sv.CombView.comb_view (s := ?s) (env := ?env) (hs := ?hs) (harity := ?harity) (h1 := ?h1)
            (hag := ?hag) (hok := ?hok) (hauto := ?hauto) (hin := ?hin) (hdisj := ?hdisj)))
      else if isBoth then
        if lexE?.isSome then
          let r ← match lexStx? with
            | some r => pure r
            | none => throwError "unreachable"
          let rT : TSyntax `term := ⟨r⟩
          let thm := mkIdent (if isShared then ``LeanModels.Sv.CombView.comb_lex_shared_view
            else ``LeanModels.Sv.CombView.comb_lex_view)
          evalTactic (← `(tactic|
            refine $thm:ident (s := ?s) (env := ?env) (hs := ?hs) (harity := ?harity) (h1 := ?h1)
              (hag := ?hag) (hok := ?hok) (hauto := ?hauto) (hin := ?hin) (hdisj := ?hdisj)
              (κ := $rT) (hrank := ?hrank)))
        else
          let r ← match rankStx? with
            | some r => pure r
            | none => throwError "unreachable"
          let rT : TSyntax `term := ⟨r⟩
          let thm := mkIdent (if isShared then ``LeanModels.Sv.CombView.comb_acyclic_shared_view
            else ``LeanModels.Sv.CombView.comb_acyclic_view)
          evalTactic (← `(tactic|
            refine $thm:ident (s := ?s) (env := ?env) (hs := ?hs) (harity := ?harity) (h1 := ?h1)
              (hag := ?hag) (hok := ?hok) (hauto := ?hauto) (hin := ?hin) (hdisj := ?hdisj)
              (ρ := $rT) (hrank := ?hrank)))
      else if lexE?.isSome then
        let r ← match lexStx? with
          | some r => pure r
          | none => throwError "unreachable"
        let rT : TSyntax `term := ⟨r⟩
        match usingStx? with
        | none =>
          evalTactic (← `(tactic|
            refine LeanModels.Sv.CombView.lex_view (s := ?s) (env := ?env) (hs := ?hs) (harity := ?harity) (h1 := ?h1)
              (hag := ?hag) (hok := ?hok) (hauto := ?hauto) (hin := ?hin) (hdisj := ?hdisj)
              (κ := $rT) (hrank := ?hrank)))
        | some u =>
          let uT : TSyntax `term := ⟨u⟩
          evalTactic (← `(tactic|
            refine LeanModels.Sv.CombView.lex_view_using (s := ?s) (env := ?env) (hs := ?hs) (harity := ?harity) (h1 := ?h1)
              (hag := ?hag) (hok := ?hok) (hauto := ?hauto) (hin := ?hin) (hc := $uT)
              (κ := $rT) (hrank := ?hrank)))
      else
        let r ← match rankStx? with
          | some r => pure r
          | none => throwError "unreachable"
        let rT : TSyntax `term := ⟨r⟩
        match usingStx? with
        | none =>
          evalTactic (← `(tactic|
            refine LeanModels.Sv.CombView.acyclic_view (s := ?s) (env := ?env) (hs := ?hs) (harity := ?harity) (h1 := ?h1)
              (hag := ?hag) (hok := ?hok) (hauto := ?hauto) (hin := ?hin) (hdisj := ?hdisj)
              (ρ := $rT) (hrank := ?hrank)))
        | some u =>
          let uT : TSyntax `term := ⟨u⟩
          evalTactic (← `(tactic|
            refine LeanModels.Sv.CombView.acyclic_view_using (s := ?s) (env := ?env) (hs := ?hs) (harity := ?harity) (h1 := ?h1)
              (hag := ?hag) (hok := ?hok) (hauto := ?hauto) (hin := ?hin) (hc := $uT)
              (ρ := $rT) (hrank := ?hrank)))
      -- name the new goals, close the structural hypotheses, keep the obligations
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
          -- false (or not evaluable): the kernel decision, for its own report, as before WP-P
          closeWith n what (← `(tactic| decide +kernel))
      closeWith `hs "the recognizer's summary could not be computed by `rfl`" (← `(tactic| rfl))
      closeWith `harity "the number of arguments differs from the number of parameters" (← `(tactic| rfl))
      closeParamEnv "sv_structure" (← find `h1)
      closeHag "sv_structure" (← find `hag) s args
      closeDecide `hok "the structural check failed"
      let mut out : Array MVarId := #[]
      let runOb (n : Name) (nm : String) (tac : TSyntax ``Lean.Parser.Tactic.tacticSeq)
          (grouped : Bool := false) : TacticM (List MVarId) := do
        let g0 ← find n
        -- WP-LIN: the obligations that are quadratic in the number of sites are first restricted to the sites
        -- that write the same signal (`groupStructureGoal`); a failure of that step keeps the original goal
        let g ← if grouped && groupMinSites ≤ s.lsites.length then
            (do
              let st ← saveState
              try
                groupStructureGoal s g0
              catch _ =>
                st.restore
                pure g0)
          else pure g0
        setGoals [g]
        svObProfile nm (evalTactic tac)
        let rest ← getGoals
        let k := rest.length
        let mut i := 0
        for g in rest do
          i := i + 1
          g.setTag (if k == 1 then Name.mkSimple nm else Name.mkSimple s!"{nm}_{i}")
        return rest
      -- A FLAT netlist (WP-P3b): when no site has a generate header and the goal mentions no free
      -- variable (no parameter), the four obligations (reads and windows in range, one driver per bit,
      -- rank) are closed statements about the site list. They are decided (`closeByDecide`) through
      -- `CombViewPlain` instead of being normalized by `simp` (two of them into one goal per pair of
      -- sites: quadratic in the number of sites). Anything else (a loop, a parameter, a statement that
      -- is false) takes the normalization below, unchanged.
      let closePlain (n : Name) (lem : Name) (what : String) : TacticM Bool := do
        tryClosePlain s (← find n) lem what
      unless (← closePlain `hauto ``LeanModels.Sv.CombView.Summary.autoObl_of_plain
          "an in-range fact of a flat netlist does not hold") do
        out := out ++ (← runOb `hauto "auto" (← `(tacticSeq|
          (try simp only [$preL,*])
          $normR:tactic
          repeat' refine And.intro ?_ ?_
          all_goals first | (intros; omega) | skip))).toArray
      unless (← closePlain `hin ``LeanModels.Sv.CombView.Summary.inRangeObl_of_plain
          "the in-range obligation of a flat netlist does not hold") do
        out := out ++ (← runOb `hin "inRange" (← `(tacticSeq|
          (try simp only [$preL,*])
          $normR:tactic
          repeat' refine And.intro ?_ ?_))).toArray
      if usingStx?.isNone then
        unless (← closePlain `hdisj ``LeanModels.Sv.CombView.Summary.disjObl_of_plain
            "the one-driver obligation of a flat netlist does not hold") do
          out := out ++ (← runOb `hdisj "driverDisjoint" (← `(tacticSeq|
            (try simp only [$preL,*])
            $normR:tactic
            repeat' refine And.intro ?_ ?_)) (grouped := true)).toArray
      if isAcyc then
        unless (← closePlain `hrank ``LeanModels.Sv.CombView.Summary.rankObl'_of_plain
            "the rank obligation of a flat netlist does not hold") do
          out := out ++ (← runOb `hrank "rankDecreases" (← `(tacticSeq|
            (try simp only [$preL,*])
            $normR:tactic
            repeat' refine And.intro ?_ ?_)) (grouped := true)).toArray
      setGoals out.toList

declare_syntax_cat svRankCat
syntax "(" &"rank" " := " term ")" : svRankCat
syntax "(" &"lexRank" " := " term ")" : svRankCat

/-- `sv_structure` — see the module docstring. -/
syntax (name := svStructure) "sv_structure" (svRankCat)? (" using " term)? : tactic

/-- `sv_structure?` prints the families, site identities and the required rank relation. -/
syntax (name := svStructureQ) "sv_structure?" : tactic

@[tactic svStructure] unsafe def evalSvStructure : Tactic := fun stx => do
  let usingStx? : Option Syntax := if stx[2].isNone then none else some stx[2][1]
  if stx[1].isNone then
    withDeepRec (runSvStructure none none usingStx? false)
  else
    let cl := stx[1][0]
    if cl[1].getAtomVal == "lexRank" then withDeepRec (runSvStructure none (some cl[3]) usingStx? false)
    else withDeepRec (runSvStructure (some cl[3]) none usingStx? false)

@[tactic svStructureQ] unsafe def evalSvStructureQ : Tactic := fun _ => withDeepRec (runSvStructure none none none true)

/-! ## `sv_interface` (WP-P, P1): the ports of a design of the fragment

```
theorem add_interface (N : Nat) (hN : 1 ≤ N) (hc : CombDesign (design.sem N)) :
    SvGolf.Tasks.Add.task.Interface N (design.sem N) := by
  sv_interface
```

proves the interface conjunct of a task statement (`t.Interface N (X.sem N)`: the design's input and
output ports are exactly `t.inputs N` and `t.outputs N`, names, order and widths) for a design the
recognizer reads, from the profile `hc : CombDesign (X.sem N)` in the context (the product of
`sv_structure`). Nothing of the soundness machinery is visible: the declarations of `X.sem N` are the
recognizer's (`decls_view`, whose hypotheses `rfl` and `decide` close: the parameter stage and the
structural check), and what remains is the arithmetic of the widths, which the tactic closes with
`simp` and `omega`. It generalizes the 23-line recipe that every proof carried until WP-P (the
`Summary.sound`/`σL`/`Aff.eval` incantation of svgolf/PROVING.md §2.2) and, unlike it, does not
re-derive the in-range obligations the profile already stands for. Designs with localparams need no
change: the valuation is `Summary.val`. -/

/-- Run the interface stage. -/
unsafe def runSvInterface : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    unless ty.isApp && ty.getAppNumArgs ≥ 3 && ty.getAppFn.isConst do
      throwError "sv_interface: the goal must be a task's interface statement `t.Interface N (X.sem N)`"
    let D := ty.appArg!
    let some (pd, args, aliased) ← findGD2A D 8
      | if (← isHD2Family D 8) then throwError (hierarchyRefusal "sv_interface")
        else throwError "sv_interface: cannot read a `load_design_sv2` family (`X.sem N`) off the design in the goal"
    let some pdName := headConst? pd
      | throwError "sv_interface: the design is not a named constant"
    -- the profile `CombDesign (X.sem N)` in the context
    let mut hc? : Option Expr := none
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      if t.getAppFn.isConstOf ``LeanModels.Sv.CombDesign && hc?.isNone then
        if ← isDefEq t.appArg! D then hc? := some d.toExpr
    let some hcE := hc?
      | throwError "sv_interface: no hypothesis `CombDesign (X.sem N)` in the context (prove it with `sv_structure`, or take it from the `CombDesign ∧ Acyclic` bundle)"
    match ← evalSummary pd with
    | .error msg => throwError "sv_interface: outside the supported fragment — {msg}"
    | .ok s =>
      let probs := s.structProblems
      unless probs.isEmpty do
        throwError "sv_interface: structural check failed:\n  {"\n  ".intercalate probs}"
      let pdId := mkIdent pdName
      let keyI := mkIdent `key
      -- the goal over the unfolded family, so that `key` rewrites it syntactically; the alias-guarded family
      -- (`X.sem N`, ls-sv 7c9b7ac59) is restated at the unguarded one (`aliasInertEq`), and so is the profile
      let D' := mkApp2 (mkConst ``LeanModels.Sv.PDesign.instantiateGD2) pd args
      let hcI ← if aliased then
          let hA ← aliasInertEq "sv_interface" D pd args
          replaceMainGoal [← rewriteDesign goal hA]
          Term.exprToSyntax (← transportDesign hcE D hA)
        else
          let ty' := ty.replace fun e => if e == D then some D' else none
          replaceMainGoal [← goal.replaceTargetDefEq ty']
          Term.exprToSyntax hcE
      evalTactic (← `(tactic|
        have $keyI:ident := LeanModels.Sv.CombView.decls_view (s := ?s) (env := ?env) (hs := ?hs)
            (h1 := ?h1) (hag := ?hag) (hok := ?hok) (hc := $hcI)))
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
          -- false (or not evaluable): the kernel decision, for its own report, as before WP-P
          closeWith n what (← `(tactic| decide +kernel))
      closeWith `hs "the recognizer's summary could not be computed by `rfl`" (← `(tactic| rfl))
      closeParamEnv "sv_interface" (← find `h1)
      closeHag "sv_interface" (← find `hag) s args
      closeDecide `hok "the structural check failed"
      setGoals [bodyGoal]
      -- unfold the statement and the task, and evaluate the declarations' widths
      let headId := mkIdent ty.getAppFn.constName!
      let taskIds : Array Ident :=
        match ty.getArg! 0 with
        | .const n _ => #[mkIdent n]
        | _ => #[]
      let taskLemmas ← taskIds.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
      try
        -- (`SvGolf` is not imported here: the names are built without macro scopes, resolved in the user's file)
        let inPorts := mkIdent `SvGolf.inputPorts
        let outPorts := mkIdent `SvGolf.outputPorts
        evalTactic (← `(tactic| simp only [$headId:ident, $inPorts:ident, $outPorts:ident]))
        evalTactic (← `(tactic| rw [$keyI:ident]))
        evalTactic (← `(tactic|
          sv_simp [LeanModels.Sv.CombView.DeclT.toDecl, LeanModels.Sv.CombView.DeclT.width,
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

/-- `sv_interface` — see the comment above. -/
syntax (name := svInterface) "sv_interface" : tactic

@[tactic svInterface] unsafe def evalSvInterface : Tactic := fun _ => withDeepRec runSvInterface
