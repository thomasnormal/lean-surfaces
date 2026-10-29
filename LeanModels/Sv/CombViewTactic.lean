import Lean
import LeanModels.Sv.CombViewDiag

/-!
# `sv_structure` / `sv_structure?`: the structural stage of the `sv_comb` tactic (v0)

```
theorem ripple_comb (N : Nat) (hN : 1 ≤ N) : CombDesign (ripple_add.sem N) := by
  sv_structure
  -- leaves ONLY the driver-window disjointness and in-range goals, as compact `∀`s
theorem ripple_acyclic (N : Nat) (hN : 1 ≤ N) : Acyclic (ripple_add.sem N) := by
  sv_structure (rank := rippleRank (fun p => if p = 0 then 0 else N + 1) (fun _ _ i => i.toNat + 1))
  -- leaves the in-range / disjointness goals and the rank-decrease goals
sv_structure?            -- prints the families, site identities and the required rank relation
```

What it does: reads the design off the goal (`X.sem N` is `PDesign.instantiateGD2 X.pdesign [↑N]`),
runs the recognizer `PDesign.summary` (a refusal is an error with the specific reason, naming
the site), applies the theorem `comb_view`/`acyclic_view` (whose hypotheses are CHECKED by `rfl`
and `decide`: the parameter stage, the structural facts, the fuel), normalizes the player
obligations, and returns them. It never discharges the in-range, disjointness or rank goals.
Before returning them it SAMPLES them at small `N` (for the message only): a genuine violation
is reported with the offending sites instead of an unprovable goal.
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
macro "sv_norm" : tactic =>
  `(tactic| simp [LeanModels.Sv.CombView.Summary.AutoObl, LeanModels.Sv.CombView.Summary.InRangeObl,
      LeanModels.Sv.CombView.Summary.DisjObl, LeanModels.Sv.CombView.Summary.RankObl,
      LeanModels.Sv.CombView.Summary.InWin, LeanModels.Sv.CombView.Summary.RdNum,
      LeanModels.Sv.CombView.Summary.dw, LeanModels.Sv.CombView.Summary.find,
      LeanModels.Sv.CombView.Summary.AD, LeanModels.Sv.CombView.TTgt.win,
      LeanModels.Sv.CombView.TRd.rd, LeanModels.Sv.CombView.TFam.Rng,
      LeanModels.Sv.CombView.Aff.eval, LeanModels.Sv.CombView.Aff.evalTerms,
      LeanModels.Sv.CombView.Aff.add, LeanModels.Sv.CombView.Aff.sub, LeanModels.Sv.CombView.Aff.neg,
      LeanModels.Sv.CombView.Aff.negTerms, LeanModels.Sv.CombView.Aff.const,
      LeanModels.Sv.CombView.Aff.var, LeanModels.Sv.CombView.DeclT.width,
      LeanModels.Sv.CombView.σL, LeanModels.Sv.CombView.bindσ, LeanModels.Sv.Win.overlaps_eq_false,
      LeanModels.Sv.Win.overlaps_eq_true, LeanModels.Sv.ReadWin.overlaps,
      LeanModels.Sv.CombView.rippleRank])

/-- Run the structural stage. (`unsafe`: it evaluates the recognizer on the design with
`evalExpr`, at tactic time only.) -/
unsafe def runSvStructure (rankStx? : Option Syntax) (hintOnly : Bool) : TacticM Unit := do
  let goal ← getMainGoal
  goal.withContext do
    let ty ← instantiateMVars (← goal.getType)
    let isComb := ty.getAppFn.isConstOf ``LeanModels.Sv.CombDesign
    let isAcyc := ty.getAppFn.isConstOf ``LeanModels.Sv.Acyclic
    unless isComb || isAcyc do
      throwError "sv_structure: the goal must be `CombDesign (X.sem N)` or `Acyclic (X.sem N)`"
    let some (pd, args) ← findGD2 ty.appArg! 8
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
      if isAcyc && rankE?.isNone then
        throwError "sv_structure: an `Acyclic` goal needs a rank over site identities, e.g. `sv_structure (rank := rippleRank … …)`; run `sv_structure?` to see the sites and the rank relation they must satisfy"
      -- sampling: genuine violations are reported with the offending sites
      for k in [lb, lb + 1, lb + 2, lb + 4] do
        let lits := fvs.map fun _ => (mkNatLit k)
        let argsK := args.replaceFVars (fvs.map mkFVar) lits
        let argVals ← evalArgs argsK
        let σ := σL (s.params.zip argVals)
        let ctxMsg := s!"(sampled at {s.params} = {argVals}; a genuine violation, not a missing proof, unless your hypotheses exclude this point)"
        if let some m := s.negCounterexample σ then
          throwError "sv_structure: in-range obligation fails — {m} {ctxMsg}"
        if let some m := s.rangeCounterexample σ then
          throwError "sv_structure: in-range obligation fails — {m} {ctxMsg}"
        if let some m := s.disjCounterexample σ then
          throwError "sv_structure: {m} {ctxMsg}"
        if let some re := rankE? then
          let reK := re.replaceFVars (fvs.map mkFVar) lits
          let ρ ← evalRank reK
          if let some m := s.rankCounterexample σ ρ then
            throwError "sv_structure: {m} {ctxMsg}"
      -- the proof
      let pdId := mkIdent pdName
      if isComb then
        evalTactic (← `(tactic|
          refine LeanModels.Sv.CombView.comb_view (s := ?s) (env := ?env) (hs := ?hs) (harity := ?harity) (h1 := ?h1)
            (hag := ?hag) (hok := ?hok) (hauto := ?hauto) (hin := ?hin) (hdisj := ?hdisj)))
      else
        let r ← match rankStx? with
          | some r => pure r
          | none => throwError "unreachable"
        let rT : TSyntax `term := ⟨r⟩
        evalTactic (← `(tactic|
          refine LeanModels.Sv.CombView.acyclic_view (s := ?s) (env := ?env) (hs := ?hs) (harity := ?harity) (h1 := ?h1)
            (hag := ?hag) (hok := ?hok) (hauto := ?hauto) (hin := ?hin) (hdisj := ?hdisj)
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
      closeWith `hs "the recognizer's summary could not be computed by `rfl`" (← `(tactic| rfl))
      closeWith `harity "the number of arguments differs from the number of parameters" (← `(tactic| rfl))
      closeWith `h1 "the parameter stage (`paramEnv2`) of this design could not be evaluated at a symbolic parameter" (← `(tactic| rfl))
      closeWith `hag "the parameter values could not be read off the instantiation environment" (← `(tactic| rfl))
      closeWith `hok "the structural check failed" (← `(tactic| decide +kernel))
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
        sv_norm
        repeat' refine And.intro ?_ ?_
        all_goals first | (intros; omega) | skip))).toArray
      out := out ++ (← runOb `hin "inRange" (← `(tacticSeq|
        (try simp only [$pdId:ident])
        sv_norm
        repeat' refine And.intro ?_ ?_))).toArray
      out := out ++ (← runOb `hdisj "driverDisjoint" (← `(tacticSeq|
        (try simp only [$pdId:ident])
        sv_norm
        repeat' refine And.intro ?_ ?_))).toArray
      if isAcyc then
        out := out ++ (← runOb `hrank "rankDecreases" (← `(tacticSeq|
          (try simp only [$pdId:ident])
          sv_norm
          repeat' refine And.intro ?_ ?_))).toArray
      setGoals out.toList

declare_syntax_cat svRankCat
syntax "(" &"rank" " := " term ")" : svRankCat

/-- `sv_structure` — see the module docstring. -/
syntax (name := svStructure) "sv_structure" (svRankCat)? : tactic

/-- `sv_structure?` prints the families, site identities and the required rank relation. -/
syntax (name := svStructureQ) "sv_structure?" : tactic

@[tactic svStructure] unsafe def evalSvStructure : Tactic := fun stx => do
  let rk? : Option Syntax := if stx[1].isNone then none else some stx[1][0][3]
  runSvStructure rk? false

@[tactic svStructureQ] unsafe def evalSvStructureQ : Tactic := fun _ => runSvStructure none true
