import LeanModels.Python.Surface

/-!
# `py_begin` / `py_loop` — the loop-ergonomics layer

The final slice of the pure-tier proof surface: a total-correctness theorem
about a single-`while`-loop Python function is proved from **two clauses** —
the invariant and the decreasing measure, written as lambdas over the loop's
`Int` variables — and nothing else. Everything the old instantiation-style
loop lemmas spelled out by hand (`tri_loop`/`gcd_loop`: logical state `σ`,
`toEnv` rendering, the test-value function `tv`, the continuation condition
`Cont`, the body's logical `step`, the two `py_threshold` interpreter
obligations, the fuel splice) is now *derived*:

* **`py_begin [prog]`** symbolically executes the function entry up to the
  loop. It proves a fuel-polymorphic entry lemma
  `hentry : ∀ F, callFunction m f args (F + 32) = <entry normal form F>`
  whose right-hand side is discovered by `py_simp` and contains the frozen
  `execWhile <m> (F + c) <env₀> <test> <body> []`. Committing the goal's fuel
  witness this early would be a scope trap (the loop's threshold `fℓ` does
  not exist yet, and an mvar created now could never be assigned an fvar
  `obtain`ed later), so the fuel stays universally quantified until `py_loop`
  splices the loop run in. `py_begin` also restates every hypothesis whose
  type mentions the `Py*` type brands (`PyInt`/`PyBool`/`PyStr`,
  definitionally `Int`/`Bool`/`String`) in the unbranded form, so `omega` and
  `grind` consume them directly in the residual goals.

* **`py_loop (inv := fun (x y : Int) => …) (dec := fun (x y : Int) => …)`**
  reads `env₀`/`test`/`body` off `hentry`, derives `σ := Int × ⋯ × Int`,
  `toEnv`, `Inv`, `μ` from the user lambdas (binder names matched against the
  loop-environment variable names), and applies the generic while rule
  `execWhile_total_of_invariant` (Surface.lean) with `tv`, `Cont`, and the
  *componentwise* `step := fun q => (?st₀ q, …)` as unification metavariables:
  the three interpreter obligations are auto-discharged by the `py_threshold`
  recipe, and closing each residue with `rfl` *assigns* the metavariables by
  Miller-pattern unification — the state variable is deliberately kept whole
  (`intro s`, never destructured) inside those obligations, and the
  branch-shaped comparison result is collapsed by `ite_ok_bool` first, because
  destructured states and surviving `ite`s are exactly the two shapes Miller
  unification cannot read a function off. Finally the tactic commits the fuel
  (`fℓ + 32`), rewrites with `hentry`, splices the loop run (threshold form,
  `execWhile_at_least`), and executes the epilogue with `py_simp`.

  Residual goals, in order — **pure mathematics, no `Val`, no fuel, no AST**,
  with tuple projections destructured to named atoms and a top-level-`∧`
  invariant split into `hinv1`, `hinv2`, … (one hypothesis per conjunct —
  `grind`'s e-matching instantiates lemmas from atomic facts, not from
  conjunctions; a non-conjunction invariant stays whole as `hinv`):
  1. *exit algebra*: loop variables as primed versions of the `inv` binder
     names (`total'`, `i'`), with the invariant at exit and `hcont`
     (negated loop test, boolean noise stripped) — conclude the
     returned-value equation;
  2. *invariant preservation*: binders named as in `inv`, plus the invariant
     conjuncts and `hcont` (the loop test);
  3. *measure decrease*: same shape, `μ (step s) < μ s` on named atoms;
  4. *initial invariant*: the invariant at the entry values.
  Any interpreter obligation the auto-discharge could not close (a shape
  outside the recipe) is appended after these rather than silently dropped.

  `(state := [a, b])` is the escape hatch for binder-name capture: the `inv`
  binder names must normally *be* the Python variable names, but when those
  names are shadowed by ambient theorem binders the invariant needs to
  mention (e.g. `gcd`'s initial values, `Examples/gcd/gcd.py`), `state`
  lists the Python variable names to use — each entry must name a variable
  in the loop's environment (matched **by name**, in any order), and the
  i-th listed name pairs with the i-th `inv`/`dec` lambda binder, freeing
  those binders to be anything (`x`, `y`, …); residual goals then display
  the lambda names.

v1 restrictions (deliberate — they match the generic while rule and every
gallery loop): one `while` per function, `Int`-valued loop variables, no
`break`/`continue`/`return` inside the body, body lands in `.next` flow.
-/

namespace LeanModels.Python

open Lean Elab Tactic Meta

/-- Collapse the branch-shaped comparison result of a symbolically executed
loop test (`if c then .ok (.bool true) else .ok (.bool false)`, the
`evalCompareChain` tail) into the single-branch normal form
`.ok (.bool (decide c))` that Miller unification can read a test-value
function off. Passed to `py_threshold` by `py_loop`'s `htest` discharge; if
the `ite` survived, `py_threshold`'s `split <;> simp_all` mop-up would
mis-assign the `tv` metavariable from one branch. -/
theorem ite_ok_bool (c : Prop) [Decidable c] :
    (if c then Res.ok (Val.bool true) else Res.ok (Val.bool false)) =
      .ok (.bool (decide c)) := by
  by_cases h : c <;> simp [h]

namespace PyLoopTactic

/-- The `Py*` type brands and their unbranded forms. `py_begin` restates
hypotheses through this map so `omega`/`grind` recognize them (the brands are
reducible abbreviations, but `omega`'s atom matching is syntactic). -/
def pyTypeBrands : List (Name × Name) :=
  [(``PyInt, ``Int), (``PyBool, ``Bool), (``PyStr, ``String)]

/-- Replace every `Py*` brand constant in `t` by its unbranded form (a
definitionally equal type — all brands are reducible abbreviations). -/
def unbrandPyTypes (t : Lean.Expr) : Lean.Expr :=
  t.replace fun e =>
    match e with
    | .const n _ => (pyTypeBrands.lookup n).map (Lean.mkConst ·)
    | _ => none

/-- Restate every local declaration whose type mentions a `Py*` brand at the
unbranded (definitionally equal) type. Declarations that fail the defeq check
are left untouched. -/
def normalizePyHyps (g : MVarId) : MetaM MVarId := do
  let decls ← g.withContext do
    pure (((← getLCtx).decls.toList.filterMap id).filter (!·.isImplementationDetail))
  let mut g := g
  for d in decls do
    let t' := unbrandPyTypes d.type
    unless t' == d.type do
      g ← try g.changeLocalDecl d.fvarId t' catch _ => pure g
  return g

/-- Parse a literal interpreter environment `[("n", Val.int n), …]` into
(name, value-expression) pairs. -/
partial def parseEnvList (e : Lean.Expr) : MetaM (Array (String × Lean.Expr)) := do
  if e.isAppOfArity ``List.cons 3 then
    let entry := e.getArg! 1
    unless entry.isAppOfArity ``Prod.mk 4 do
      throwError "py_loop: environment entry is not a literal pair:{indentExpr entry}"
    let .lit (.strVal name) := entry.getArg! 2
      | throwError "py_loop: environment name is not a string literal:{indentExpr (entry.getArg! 2)}"
    return #[(name, entry.getArg! 3)] ++ (← parseEnvList (e.getArg! 2))
  else if e.isAppOfArity ``List.nil 1 then
    return #[]
  else
    throwError "py_loop: loop environment is not a literal list:{indentExpr e}"

/-- Rebuild an environment literal with the named entries' values replaced by
`Val.int <replacement>` — this is how `toEnv` is derived from `env₀`. -/
partial def rebuildEnv (repl : Array (String × Lean.Expr)) (e : Lean.Expr) :
    MetaM Lean.Expr := do
  if e.isAppOfArity ``List.cons 3 then
    let entry := e.getArg! 1
    let rest ← rebuildEnv repl (e.getArg! 2)
    let .lit (.strVal name) := entry.getArg! 2
      | throwError "py_loop: malformed environment entry"
    let entry' ←
      match repl.find? (·.1 == name) with
      | some (_, proj) => do
          let newVal ← mkAppM ``Val.int #[proj]
          pure (mkAppN entry.getAppFn ((entry.getAppArgs).set! 3 newVal))
      | none => pure entry
    return mkAppN e.getAppFn ((e.getAppArgs).set! 1 entry' |>.set! 2 rest)
  else
    return e

/-- Leading lambda binder names of an elaborated user clause. -/
partial def lamBinderNames : Lean.Expr → Array Name
  | .lam n _ b _ => #[n] ++ lamBinderNames b
  | .mdata _ b => lamBinderNames b
  | _ => #[]

/-- Right-nested tuple of the given components. -/
partial def mkTupleE (xs : Array Lean.Expr) (i : Nat := 0) : MetaM Lean.Expr := do
  if i + 1 == xs.size then return xs[i]!
  else mkAppM ``Prod.mk #[xs[i]!, ← mkTupleE xs (i + 1)]

/-- Projections `p.1, p.2.1, …` of `p` into `k` components (right-nested). -/
def mkProjs (p : Lean.Expr) (k : Nat) : MetaM (Array Lean.Expr) := do
  let mut out := #[]
  let mut cur := p
  for j in [0:k] do
    if j + 1 == k then
      out := out.push cur
    else
      out := out.push (← mkAppM ``Prod.fst #[cur])
      cur ← mkAppM ``Prod.snd #[cur]
  return out

/-- The pieces of the frozen loop occurrence inside `hentry`. -/
structure LoopParts where
  mE : Lean.Expr
  envE : Lean.Expr
  testE : Lean.Expr
  bodyE : Lean.Expr
  entries : Array (String × Lean.Expr)

/-- Find the (first) `execWhile` application with a closed literal environment
inside a possibly `∀ F`-quantified statement, and split out its parts. -/
def extractLoop (statement : Lean.Expr) : MetaM LoopParts := do
  forallTelescope statement fun _ concl => do
    let some ew := concl.find? fun e =>
        e.isAppOfArity ``execWhile 6 &&
        !(e.getArg! 2).hasLooseBVars && !(e.getArg! 0).hasLooseBVars
      | throwError "py_loop: no `execWhile` occurrence found in `hentry` — is there a loop?"
    let args := ew.getAppArgs
    for i in [3:5] do
      if (args[i]!).hasLooseBVars then
        throwError "py_loop: the loop test/body depend on the fuel binder — unsupported shape"
    let entries ← parseEnvList args[2]!
    return { mE := args[0]!, envE := args[2]!, testE := args[3]!,
             bodyE := args[4]!, entries }

/-- Split a single-constructor two-field hypothesis (`∃`/`∧`/`×`) into two
named parts. Returns the two field `FVarId`s and the new goal. -/
def casesTwo (g : MVarId) (fv : FVarId) (n₁ n₂ : Name) :
    MetaM (FVarId × FVarId × MVarId) := do
  let #[sub] ← g.cases fv #[{ varNames := [n₁, n₂] }]
    | throwError "py_loop: internal — expected a single case"
  return (sub.fields[0]!.fvarId!, sub.fields[1]!.fvarId!, sub.mvarId)

/-- Destructure a right-nested product variable into components with the given
user-facing names (accessible, no hygiene marks). -/
partial def destructState (g : MVarId) (fv : FVarId) : List Name → MetaM MVarId
  | [] => return g
  | [n] => g.rename fv n
  | n :: rest => do
      let (_, sndFv, g) ← casesTwo g fv n `sRest
      destructState g sndFv rest

/-- Find a hypothesis by (accessible) user name. -/
def findHyp (g : MVarId) (n : Name) : MetaM FVarId := do
  g.withContext do
    let some d := (← getLCtx).findFromUserName? n
      | throwError "py_loop: internal — hypothesis `{n}` not found"
    return d.fvarId

/-- Destructure a top-level `∧`-chain hypothesis into separate hypotheses
`{base}1`, `{base}2`, … — `grind`'s e-matching instantiates lemmas from
atomic facts far more reliably than from one conjunction. A non-conjunction
hypothesis is left untouched (under its original name). -/
partial def splitAndHyp (g : MVarId) (fv : FVarId) (base : String) (i : Nat := 1) :
    MetaM MVarId := do
  let t ← g.withContext do
    return (← instantiateMVars (← fv.getDecl).type).cleanupAnnotations
  if t.isAppOfArity ``And 2 then
    let (_, sndFv, g) ← casesTwo g fv (Name.mkSimple s!"{base}{i}")
      (Name.mkSimple s!"{base}Rest")
    splitAndHyp g sndFv base (i + 1)
  else if i == 1 then
    return g
  else
    g.rename fv (Name.mkSimple s!"{base}{i}")

/-- Intro `∀ s, Inv s → Cont s = true → …` with accessible names and the state
destructured to the user's binder names: the "clean form" of the
invariant-preservation and measure-decrease goals. -/
def introMathGoal (g : MVarId) (names : List Name) : MetaM MVarId := do
  let (sFv, g) ← g.intro `s
  let (_, g) ← g.intro `hinv
  let (_, g) ← g.intro `hcont
  destructState g sFv names

end PyLoopTactic

open PyLoopTactic

/-- `py_begin [prog]` — symbolically execute the entry of the function under
proof up to (and freezing at) its `while` loop. Works on a `==>`/`⇓`
(`CallsTo`) goal; adds
`hentry : ∀ F, callFunction m f args (F + 32) = <entry normal form F>`
to the context (fuel-polymorphic — the fuel witness is committed only by
`py_loop`, which needs the loop threshold first) and restates `Py*`-branded
hypotheses in their unbranded (`Int`/`Bool`/`String`) forms for
`omega`/`grind`. The right-hand side is captured from `py_simp`'s
normalization into a synthetic-opaque metavariable (opaque so no simp lemma
can mis-assign it mid-flight) and contains the frozen
`execWhile <m> (F + c) <env₀> <test> <body> []` that `py_loop` consumes.
Pass the loaded program literal (`py_begin [tri]`). -/
elab "py_begin" "[" prog:ident "]" : tactic => do
  withMainContext do
    let g ← getMainGoal
    let g ← normalizePyHyps g
    replaceMainGoal [g]
  withMainContext do
    let g ← getMainGoal
    let tgt := (← instantiateMVars (← g.getType)).cleanupAnnotations
    let tgt ← if tgt.isAppOfArity ``CallsTo 4 then pure tgt else whnfR tgt
    unless tgt.isAppOfArity ``CallsTo 4 do
      throwError "py_begin: goal is not a `==>`/`⇓` (CallsTo) statement:{indentExpr tgt}"
    let mE := tgt.getArg! 0
    let fE := tgt.getArg! 1
    let argsE := tgt.getArg! 2
    let natT := Lean.mkConst ``Nat
    let resValT ← mkAppM ``Res #[Lean.mkConst ``Val]
    let restM ← mkFreshExprMVar (← mkArrow natT resValT) .syntheticOpaque `pyEntryRest
    let entryTy ← withLocalDeclD `F natT fun F => do
      let fuel ← mkAppM ``HAdd.hAdd #[F, mkNatLit 32]
      let call ← mkAppM ``callFunction #[mE, fE, argsE, fuel]
      mkForallFVars #[F] (← mkEq call (mkApp restM F))
    let entryG ← mkFreshExprMVar entryTy .syntheticOpaque `pyEntry
    let saved ← getGoals
    setGoals [entryG.mvarId!]
    let progT : Term := ⟨prog.raw⟩
    evalTactic (← `(tactic|
      (intro F; simp only [$progT:term]; py_simp [callFunction.eq_2])))
    let [g2] ← getGoals
      | throwError "py_begin: expected exactly one residual entry goal"
    g2.withContext do
      let ty ← instantiateMVars (← g2.getType)
      let some (_, lhs, rhs) := ty.eq?
        | throwError "py_begin: entry goal is not an equation:{indentExpr ty}"
      unless rhs.isApp && rhs.appFn!.isMVar do
        throwError "py_begin: entry right-hand side is not the capture mvar:{indentExpr rhs}"
      let lam ← mkLambdaFVars #[rhs.appArg!] lhs
      restM.mvarId!.assign lam
    setGoals [g2]
    evalTactic (← `(tactic| rfl))
    setGoals saved
    let g ← getMainGoal
    let g ← g.assert `hentry (← instantiateMVars entryTy) entryG
    let (_, g) ← g.intro1P
    replaceMainGoal [g]

/-- The worker behind `py_loop` (documented on the syntax below). -/
def runPyLoop (stateNames? : Option (Array Name)) (inv dec : Term) : TacticM Unit := do
  withMainContext do
    -- (a) the frozen loop, from `hentry`
    let some hd := (← getLCtx).findFromUserName? `hentry
      | throwError "py_loop: no `hentry` hypothesis in context — run `py_begin [<prog>]` first"
    let parts ← extractLoop (← instantiateMVars hd.type)
    -- (b) the user clauses and the loop variables
    let invU ← instantiateMVars (← Term.withSynthesize (Term.elabTerm inv none))
    let decU ← instantiateMVars (← Term.withSynthesize (Term.elabTerm dec none))
    let binders := lamBinderNames invU
    let k := binders.size
    if k == 0 then
      throwError "py_loop: `inv` must be an explicit lambda over the loop's Int variables"
    unless (lamBinderNames decU).size == k do
      throwError "py_loop: `dec` must bind exactly the {k} variables of `inv`"
    let stateNames := stateNames?.getD binders
    unless stateNames.size == k do
      throwError "py_loop: `state` names {stateNames.size} variables, `inv` binds {k}"
    let mut initVals : Array Lean.Expr := #[]
    for nm in stateNames do
      let some (_, valE) := parts.entries.find? (·.1 == nm.toString)
        | throwError "py_loop: loop variable `{nm}` is not in the loop environment {parts.entries.map (·.1)} — when the Python variable names are shadowed by ambient binders, name them with `(state := [...])`"
      unless valE.isAppOfArity ``Val.int 1 do
        throwError "py_loop: environment entry `{nm}` is not `Val.int`-valued:{indentExpr valE}"
      initVals := initVals.push (valE.getArg! 0)
    -- (c) σ, toEnv, Inv, μ; tv/Cont/step as natural (assignable) mvars
    let intT := Lean.mkConst ``Int
    let mut σ := intT
    for _ in [0:k-1] do σ ← mkAppM ``Prod #[intT, σ]
    let toEnvFn ← withLocalDeclD `p σ fun p => do
      let projs ← mkProjs p k
      let repl := (stateNames.map (·.toString)).zip projs
      mkLambdaFVars #[p] (← rebuildEnv repl parts.envE)
    let invFn ← withLocalDeclD `p σ fun p => do
      mkLambdaFVars #[p] (mkAppN invU (← mkProjs p k)).headBeta
    let muFn ← withLocalDeclD `p σ fun p => do
      mkLambdaFVars #[p] (mkAppN decU (← mkProjs p k)).headBeta
    let contM ← mkFreshExprMVar (← mkArrow σ (Lean.mkConst ``Bool)) .natural `Cont
    let tvM ← mkFreshExprMVar (← mkArrow σ (Lean.mkConst ``Val)) .natural `tv
    let mut stMs : Array Lean.Expr := #[]
    for j in [0:k] do
      stMs := stMs.push
        (← mkFreshExprMVar (← mkArrow σ intT) .natural (Name.mkSimple s!"st{j}"))
    let stepFn ← withLocalDeclD `q σ fun q => do
      mkLambdaFVars #[q] (← mkTupleE (stMs.map (mkApp · q)))
    -- (d) the generic while rule, obligations as natural mvars
    let rule ← mkAppM ``execWhile_total_of_invariant
      #[parts.mE, parts.testE, parts.bodyE, toEnvFn, invFn, contM, stepFn, muFn, tvM]
    let (hyps, _, _) ← forallMetaBoundedTelescope (← inferType rule) 5
    unless hyps.size == 5 do throwError "py_loop: internal — unexpected rule shape"
    let s0 ← mkTupleE initVals
    let hs0 ← mkFreshExprMVar ((mkApp invFn s0).headBeta) .syntheticOpaque `hinit
    let hloopE := mkAppN rule (hyps ++ #[s0, hs0])
    -- (e) auto-discharge the interpreter obligations; the closing `rfl`s
    -- assign tv/Cont/step by Miller-pattern unification (state kept whole)
    let saved ← getGoals
    let mut interpLeft : List MVarId := []
    setGoals [hyps[0]!.mvarId!]   -- htest
    evalTactic (← `(tactic| (intro s _hs; py_threshold 32 [ite_ok_bool]; try rfl)))
    interpLeft := interpLeft ++ (← getGoals)
    unless ← tvM.mvarId!.isAssigned do
      throwError "py_loop: could not derive the loop-test value (the `htest` obligation did not close — test shape outside the v1 recipe)"
    setGoals [hyps[1]!.mvarId!]   -- htv
    -- `simp only [truthy]`, not `py_simp`: the full simp set moves `!` across
    -- the equation (`(b == 0) = !?Cont s`), destroying the Miller pattern
    evalTactic (← `(tactic| (intro s _hs; try simp only [truthy]; try rfl)))
    interpLeft := interpLeft ++ (← getGoals)
    unless ← contM.mvarId!.isAssigned do
      throwError "py_loop: could not derive the continuation condition (the `htv` obligation did not close)"
    setGoals [hyps[2]!.mvarId!]   -- hbody
    evalTactic (← `(tactic|
      (intro s _hs hc
       try simp only [decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne] at hc
       py_threshold 32 [hc]
       try (first
         | rfl
         | exact ⟨rfl, rfl⟩
         | exact ⟨rfl, rfl, rfl⟩
         | exact ⟨rfl, rfl, rfl, rfl⟩))))
    interpLeft := interpLeft ++ (← getGoals)
    for st in stMs do
      unless ← st.mvarId!.isAssigned do
        throwError "py_loop: could not derive the body's logical step (the `hbody` obligation did not close — body shape outside the v1 recipe)"
    -- (f) restate the math obligations in clean, named form
    let hcontSimp ← `(tactic|
      try simp only [decide_eq_true_eq, Bool.not_eq_true', beq_eq_false_iff_ne]
        at $(mkIdent `hcont):ident)
    let mut mathGoals : List MVarId := []
    for i in [3:5] do              -- hinv, hdec
      let gm ← introMathGoal hyps[i]!.mvarId! binders.toList
      setGoals [gm]
      evalTactic hcontSimp
      evalTactic (← `(tactic| try simp only [] at $(mkIdent `hinv):ident))
      evalTactic (← `(tactic| try simp only []))
      evalTactic (← `(tactic| try clear $(mkIdent `hentry):ident))
      for g in ← getGoals do
        let g ← try splitAndHyp g (← findHyp g `hinv) "hinv" catch _ => pure g
        mathGoals := mathGoals ++ [g]
    setGoals [hs0.mvarId!]         -- initial invariant
    evalTactic (← `(tactic| try simp only []))
    evalTactic (← `(tactic| try clear $(mkIdent `hentry):ident))
    mathGoals := mathGoals ++ (← getGoals)
    -- (g) main goal: destructure the loop fact, commit fuel, splice, execute
    -- the epilogue; what remains is the exit algebra
    setGoals saved
    let g ← getMainGoal
    let hloopE ← instantiateMVars hloopE
    let g ← g.assert `hloop (← inferType hloopE) hloopE
    let (hloopFv, g) ← g.intro1P
    let (sFv, hFv, g) ← casesTwo g hloopFv `s' `hAnd
    let (_, h2Fv, g) ← casesTwo g hFv `hinv `hAnd2
    let (_, _, g) ← casesTwo g h2Fv `hcont `hex
    let primed := binders.toList.map fun n => Name.mkSimple (n.toString ++ "'")
    let g ← destructState g sFv primed
    let g ← (do
      let hexFv ← findHyp g `hex
      g.withContext do
        let hlE ← mkAppM ``execWhile_at_least #[Lean.mkFVar hexFv]
        let g ← g.assert `hlp (← inferType hlE) hlE
        g.intro1P)
      >>= fun (_, g) => pure g
    let (_, _, g) ← casesTwo g (← findHyp g `hlp) `fl `hl
    let g ← try g.clear (← findHyp g `hex) catch _ => pure g
    setGoals [g]
    let hinvId := mkIdent `hinv
    let hcontId := mkIdent `hcont
    let flId := mkIdent `fl
    let hlId := mkIdent `hl
    let hentryId := mkIdent `hentry
    evalTactic (← `(tactic|
      (try simp only [] at $hinvId:ident
       try simp only [decide_eq_false_iff_not, Bool.not_eq_false', beq_iff_eq,
                      Decidable.not_not] at $hcontId:ident
       refine ⟨$flId + 32, ?_⟩
       rw [$hentryId:term]
       rw [$hlId:term]
       rotate_left
       · omega
       py_simp
       all_goals try clear $hlId $flId $hentryId)))
    let mut mainLeft : List MVarId := []
    for g in ← getGoals do
      let g ← try splitAndHyp g (← findHyp g `hinv) "hinv" catch _ => pure g
      mainLeft := mainLeft ++ [g]
    setGoals (mainLeft ++ mathGoals ++ interpLeft)

/-- `py_loop (inv := fun (x y : Int) => …) (dec := fun (x y : Int) => …)` —
prove the `while` loop frozen inside `hentry` (from `py_begin`) via the
generic while rule, from just an invariant and a decreasing `Nat` measure
written over the loop's `Int` variables. Binder names must be the Python
variable names (they select the loop variables from the environment);
`(state := [a, b])`, given *before* `inv`, names the environment variables
positionally instead — the escape hatch for when ambient theorem binders
shadow the Python names and the invariant must mention them (initial values,
`Examples/gcd/gcd.py`). Residual goals (exit algebra with primed
variables, invariant preservation, measure decrease, initial invariant) are
pure mathematics over named atoms, the invariant's conjuncts split into
`hinv1`, `hinv2`, … and the loop test as `hcont` — see the module
docstring. -/
elab (name := pyLoopWithState) "py_loop" "(" &"state" " := " "[" ids:ident,* "]" ")"
    "(" &"inv" " := " inv:term ")" "(" &"dec" " := " dec:term ")" : tactic => do
  runPyLoop (some (ids.getElems.map (·.getId))) inv dec

@[inherit_doc pyLoopWithState]
elab "py_loop" "(" &"inv" " := " inv:term ")" "(" &"dec" " := " dec:term ")" : tactic => do
  runPyLoop none inv dec

end LeanModels.Python
