import Lean
import LeanModels.Sv.CombViewDiag
import LeanModels.Sv.CombViewPlain

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

What it does: reads the design off the goal (`X.sem N` is `PDesign.instantiateGD2 X.pdesign [↑N]`),
runs the recognizer `PDesign.summary` (a refusal is an error with the specific reason, naming
the site), applies the theorem `comb_view`/`acyclic_view` (whose hypotheses are CHECKED by `rfl`
and `decide`: the parameter stage, the structural facts, the fuel), normalizes the player
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
-/

open Lean Elab Tactic Meta

open LeanModels.Sv.CombView

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


/-- `X.sem N` is `PDesign.instantiateGD2 X.pdesign [↑N]`: unfold until it shows. -/
private partial def findGD2 (e : Expr) (fuel : Nat) : MetaM (Option (Expr × Expr)) := do
  let e ← whnfCore e
  if e.isAppOfArity ``LeanModels.Sv.PDesign.instantiateGD2 2 then
    return some (e.getAppArgs[0]!, e.getAppArgs[1]!)
  match fuel with
  | 0 => return none
  | fuel + 1 =>
    match ← unfoldDefinition? e with
    | some e' => findGD2 e' fuel
    | none => return none

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
  | `(tactic| sv_norm) => `(tactic| (sv_norm_core; sv_lp_norm; try simp))
  | `(tactic| sv_norm [$ids,*]) =>
      `(tactic| (sv_norm_core; sv_lp_norm; (try simp (config := { maxSteps := 4000000 }) only [$ids,*]); try simp))

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

/-- Run the structural stage. (`unsafe`: it evaluates the recognizer on the design with
`evalExpr`, at tactic time only.) -/
unsafe def runSvStructure (rankStx? lexStx? usingStx? : Option Syntax) (hintOnly : Bool) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    -- the bundle `CombDesign D ∧ Acyclic D` (WP-P): one application of `Summary.sound`, one round of
    -- obligations for both
    let isBoth := ty.isAppOfArity ``And 2 &&
      ty.appFn!.appArg!.getAppFn.isConstOf ``LeanModels.Sv.CombDesign &&
      ty.appArg!.getAppFn.isConstOf ``LeanModels.Sv.Acyclic
    let isComb := ty.getAppFn.isConstOf ``LeanModels.Sv.CombDesign
    let isAcyc := ty.getAppFn.isConstOf ``LeanModels.Sv.Acyclic || isBoth
    unless isComb || isAcyc do
      throwError "sv_structure: the goal must be `CombDesign (X.sem N)`, `Acyclic (X.sem N)` or their conjunction `CombDesign (X.sem N) ∧ Acyclic (X.sem N)`"
    let dGoal := if isBoth then ty.appFn!.appArg!.appArg! else ty.appArg!
    let some (pd, args) ← findGD2 dGoal 8
      | throwError "sv_structure: cannot read a `load_design_sv2` family (`X.sem N`) off the design in the goal"
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
      let pdId := mkIdent pdName
      -- the player's own rank/key function, if it is a named definition: unfold it
      let keyIds : Array Ident :=
        match (rankE?.orElse fun _ => lexE?) with
        | some e =>
            match e.getAppFn with
            | .const n _ => #[mkIdent n]
            | _ => #[]
        | none => #[]
      let keyLemmas ← keyIds.mapM fun i => `(Lean.Parser.Tactic.simpLemma| $i:ident)
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
          evalTactic (← `(tactic|
            refine LeanModels.Sv.CombView.comb_lex_view (s := ?s) (env := ?env) (hs := ?hs) (harity := ?harity) (h1 := ?h1)
              (hag := ?hag) (hok := ?hok) (hauto := ?hauto) (hin := ?hin) (hdisj := ?hdisj)
              (κ := $rT) (hrank := ?hrank)))
        else
          let r ← match rankStx? with
            | some r => pure r
            | none => throwError "unreachable"
          let rT : TSyntax `term := ⟨r⟩
          evalTactic (← `(tactic|
            refine LeanModels.Sv.CombView.comb_acyclic_view (s := ?s) (env := ?env) (hs := ?hs) (harity := ?harity) (h1 := ?h1)
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
          (try simp only [$pdId:ident])
          sv_norm [$keyLemmas,*]
          repeat' refine And.intro ?_ ?_
          all_goals first | (intros; omega) | skip))).toArray
      unless (← closePlain `hin ``LeanModels.Sv.CombView.Summary.inRangeObl_of_plain
          "the in-range obligation of a flat netlist does not hold") do
        out := out ++ (← runOb `hin "inRange" (← `(tacticSeq|
          (try simp only [$pdId:ident])
          sv_norm [$keyLemmas,*]
          repeat' refine And.intro ?_ ?_))).toArray
      if usingStx?.isNone then
        unless (← closePlain `hdisj ``LeanModels.Sv.CombView.Summary.disjObl_of_plain
            "the one-driver obligation of a flat netlist does not hold") do
          out := out ++ (← runOb `hdisj "driverDisjoint" (← `(tacticSeq|
            (try simp only [$pdId:ident])
            sv_norm [$keyLemmas,*]
            repeat' refine And.intro ?_ ?_))).toArray
      if isAcyc then
        unless (← closePlain `hrank ``LeanModels.Sv.CombView.Summary.rankObl'_of_plain
            "the rank obligation of a flat netlist does not hold") do
          out := out ++ (← runOb `hrank "rankDecreases" (← `(tacticSeq|
            (try simp only [$pdId:ident])
            sv_norm [$keyLemmas,*]
            repeat' refine And.intro ?_ ?_))).toArray
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
    let some (pd, args) ← findGD2 D 8
      | throwError "sv_interface: cannot read a `load_design_sv2` family (`X.sem N`) off the design in the goal"
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
      let hcI ← Term.exprToSyntax hcE
      let keyI := mkIdent `key
      -- the goal over the unfolded family, so that `key` rewrites it syntactically
      let D' := mkApp2 (mkConst ``LeanModels.Sv.PDesign.instantiateGD2) pd args
      let ty' := ty.replace fun e => if e == D then some D' else none
      replaceMainGoal [← goal.replaceTargetDefEq ty']
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
      closeWith `h1 "the parameter stage (`paramEnv2`) of this design could not be evaluated at a symbolic parameter" (← `(tactic| rfl))
      closeWith `hag "the parameter values could not be read off the instantiation environment" (← `(tactic| rfl))
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

/-- `sv_interface` — see the comment above. -/
syntax (name := svInterface) "sv_interface" : tactic

@[tactic svInterface] unsafe def evalSvInterface : Tactic := fun _ => withDeepRec runSvInterface
