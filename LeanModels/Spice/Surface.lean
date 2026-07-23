import Lean
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import LeanModels.Python.Surface
import LeanModels.Spice.Json
import LeanModels.Spice.Semantics
import LeanModels.Spice.Solve

/-!
# SPICE specification surface

`load_netlist` turns an extracted JSON envelope into a literal `Netlist` at
elaboration time. The `⊨dc` judgment is universal: every assignment obeying
the flattened physical laws must satisfy the stated property.
-/

namespace LeanModels.Spice

/-! ## Literal ingestion -/

deriving instance Lean.ToExpr for Span
deriving instance Lean.ToExpr for ElementKind
deriving instance Lean.ToExpr for Element
deriving instance Lean.ToExpr for MosPolarity
deriving instance Lean.ToExpr for Mosfet
deriving instance Lean.ToExpr for MosParameter
deriving instance Lean.ToExpr for MosModel
deriving instance Lean.ToExpr for Instance
deriving instance Lean.ToExpr for Unsupported
deriving instance Lean.ToExpr for Card
deriving instance Lean.ToExpr for Subckt
deriving instance Lean.ToExpr for SubcktEntry
deriving instance Lean.ToExpr for Netlist
deriving instance Lean.ToExpr for FlatNetlist
deriving instance Lean.ToExpr for Unknown
deriving instance Lean.ToExpr for Solution

open Lean Elab Command in
/-- Read a `spice-0.1` envelope at elaboration time and declare a literal
`Netlist`. Successful flattening and solving also declare four companion
artifacts: `<name>_flat`, `<name>_flatten`, `<name>_solution`, and
`<name>_solution_satisfies`. The path is relative to the package root under
`lake build`. -/
elab "load_netlist " name:ident " from " path:str : command => do
  let pathString := path.getString
  let contents ←
    match ← (IO.FS.readFile ⟨pathString⟩).toBaseIO with
    | .ok contents => pure contents
    | .error error =>
        throwErrorAt path "load_netlist: cannot read '{pathString}': {toString error}"
  let envelope ←
    match parseEnvelopeString contents with
    | .ok envelope => pure envelope
    | .error error =>
        throwErrorAt path "load_netlist: invalid envelope '{pathString}': {error}"
  let declarationName := (← getCurrNamespace) ++ name.getId
  if (← getEnv).contains declarationName then
    throwErrorAt name "load_netlist: '{declarationName}' has already been declared"
  let companionName (suffix : String) : Name :=
    .str declarationName.getPrefix (declarationName.getString! ++ suffix)
  let flatResult := flatten envelope.netlist
  let solvedResult :=
    match flatResult with
    | .ok flat => (solveData flat).toOption
    | .error _ => none
  liftCoreM do
    addAndCompile <| .defnDecl {
      name := declarationName
      levelParams := []
      type := Lean.mkApp (Lean.mkConst ``LeanModels.Spice.Netlist)
        (Lean.mkConst ``Rat)
      value := Lean.toExpr envelope.netlist
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst declarationName
    addDocStringCore declarationName
      s!"SPICE netlist loaded from `{pathString}` (source `{envelope.sourceFile}`, sha256 `{envelope.sourceSha256}`)."
    if let .ok flat := flatResult then
      let flatName := companionName "_flat"
      addAndCompile <| .defnDecl {
        name := flatName
        levelParams := []
        type := Lean.mkApp (Lean.mkConst ``LeanModels.Spice.FlatNetlist)
          (Lean.mkConst ``Rat)
        value := Lean.toExpr flat
        hints := .abbrev
        safety := .safe }
      enableRealizationsForConst flatName
      addDocStringCore flatName
        s!"Exact hierarchy-free form generated from `{declarationName}`."
    if let some solution := solvedResult then
      let solutionName := companionName "_solution"
      addAndCompile <| .defnDecl {
        name := solutionName
        levelParams := []
        type := Lean.mkConst ``LeanModels.Spice.Solution
        value := Lean.toExpr solution
        hints := .abbrev
        safety := .safe }
      enableRealizationsForConst solutionName
      addDocStringCore solutionName
        s!"Exact finite MNA solution generated from `{declarationName}`."
  if let .ok _ := flatResult then
    let flatName := companionName "_flat"
    let flattenName := companionName "_flatten"
    let netlistId := mkIdent declarationName
    let flatId := mkIdent flatName
    let flattenId := mkIdent (.mkSimple flattenName.getString!)
    elabCommand (← `(theorem $flattenId :
      flatten $netlistId = .ok $flatId := by rfl))
  if let some _ := solvedResult then
    let flatName := companionName "_flat"
    let solutionName := companionName "_solution"
    let satisfiesName := companionName "_solution_satisfies"
    let flatId := mkIdent flatName
    let solutionId := mkIdent solutionName
    let satisfiesId := mkIdent (.mkSimple satisfiesName.getString!)
    elabCommand (← `(theorem $satisfiesId :
      Satisfies $flatId ($solutionId).assignment := by
        unfold $flatId $solutionId
        simp [Satisfies, FlatNetlist.nodes,
          kclSum, currentInto, deviceLawHolds, Solution.assignment,
          assignmentOf]
        norm_num))
  liftTermElabM do
    Term.addTermInfo' name (Lean.mkConst declarationName) (isBinder := true)

macro "#print_netlist " name:ident : command => `(#eval (repr $name))

open Lean Elab Command in
/-- Print the exact rational operating point generated by `load_netlist`. -/
elab "#spice_op " name:ident : command => do
  let base ← resolveGlobalConstNoOverload name
  let solutionName :=
    .str base.getPrefix (base.getString! ++ "_solution")
  unless (← getEnv).contains solutionName do
    throwErrorAt name "#spice_op: `{base}` has no generated solution; \
      the circuit may be singular or unsupported"
  let solution : Term := ⟨(mkIdent solutionName).raw⟩
  elabCommand (← `(#eval IO.println (Solution.describe $solution:term)))

open Lean Elab Command in
/-- Print the exact augmented MNA equations generated from a loaded netlist. -/
elab "#spice_equations " name:ident : command => do
  let base ← resolveGlobalConstNoOverload name
  let flatName :=
    .str base.getPrefix (base.getString! ++ "_flat")
  unless (← getEnv).contains flatName do
    throwErrorAt name "#spice_equations: `{base}` has no generated flat netlist"
  let flat : Term := ⟨(mkIdent flatName).raw⟩
  elabCommand (← `(#eval IO.println (LinearSystem.describe (assemble $flat:term))))

/-! ## Universal DC judgment -/

/-- Every physically admissible DC assignment satisfies `property`. -/
def DCModels (netlist : Netlist) (property : Assignment → Prop) : Prop :=
  ∀ assignment, SatisfiesNetlist netlist assignment → property assignment

/-- Surface form with explicit voltage/current accessor binders:
`divider ⊨dc { v, i => v "out" = 10 / 3 }`. -/
syntax:50 term:51 " ⊨dc " "{" ident ", " ident " => " term "}" : term
macro_rules
  | `($netlist ⊨dc { $voltage, $current => $property }) =>
      `(DCModels $netlist (fun assignment =>
          let $voltage := assignment.volt
          let $current := assignment.cur
          $property))

/-- Predicate-level form for contracts that already name an assignment. -/
infix:50 " ⊨dc? " => DCModels

/-- Concrete non-vacuity check through hierarchy flattening and the exact
checked MNA solver. -/
macro "#spice_check " netlist:term " shows " node:str " = " value:term : command =>
  `(#guard
      match flatten $netlist with
      | .ok flat =>
          match solve flat with
          | .ok assignment => assignment.volt $node == $value
          | .error _ => false
      | .error _ => false)

namespace SpiceSolveTactic

open Lean Elab Tactic

private def companionName (base : Name) (suffix : String) : Name :=
  .str base.getPrefix (base.getString! ++ suffix)

private def requireCompanions (base : Name) : TacticM Unit := do
  let env ← getEnv
  for suffix in ["_flat", "_flatten", "_solution", "_solution_satisfies"] do
    let name := companionName base suffix
    unless env.contains name do
      throwError "spice_solve: missing generated declaration `{name}`; \
        ensure `{base}` was introduced by `load_netlist` and has a nonsingular DC solution"

private def run (base : Name) : TacticM Unit := do
  requireCompanions base
  let identFor (suffix : String) := mkIdent (companionName base suffix)
  let flat : Term := ⟨(identFor "_flat").raw⟩
  let flattenEq : Term := ⟨(identFor "_flatten").raw⟩
  let solution : Term := ⟨(identFor "_solution").raw⟩
  let solutionSatisfies : Term := ⟨(identFor "_solution_satisfies").raw⟩
  evalTactic (← `(tactic| first
    | (intro assignment h
       unfold SatisfiesNetlist at h
       rw [$flattenEq:term] at h
       simp [Satisfies, $flat:term, FlatNetlist.nodes, kclSum, currentInto,
         deviceLawHolds] at h
       grind)
    | (refine ⟨$flat:term, $flattenEq:term, ($solution:term).assignment,
         $solutionSatisfies:term, ?_⟩
       intro other h
       simp [Satisfies, $flat:term, FlatNetlist.nodes, kclSum, currentInto,
         deviceLawHolds] at h
       simp [SupportEq, $flat:term, $solution:term, Solution.assignment,
         assignmentOf, FlatNetlist.nodes, FlatNetlist.branchNames]
       grind)))

private def baseFromGoal : TacticM Name := withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).cleanupAnnotations
  let netlist ←
    if target.isAppOfArity ``DCModels 2 then pure (target.getArg! 0)
    else if target.isAppOfArity ``WellPosed 1 then pure (target.getArg! 0)
    else
      throwError "spice_solve: expected a `⊨dc` or `WellPosed` goal; \
        use `spice_solve [netlist]` if the netlist cannot be inferred"
  match netlist.getAppFn.constName? with
  | some name => pure name
  | none =>
      throwError "spice_solve: the goal's netlist is not a loaded constant; \
        use `spice_solve [netlist]`"

end SpiceSolveTactic

open Lean Elab Tactic in
/-- Prove a concrete universal DC property or `WellPosed` goal from the
generated flattened equations and exact solution. The executable solver
supplies data; the generated satisfaction certificate and equation proof are
kernel-checked. The netlist is inferred from the goal. -/
elab "spice_solve" : tactic => do
  SpiceSolveTactic.run (← SpiceSolveTactic.baseFromGoal)

open Lean Elab Tactic in
/-- Explicit-netlist form of `spice_solve`. -/
elab "spice_solve" "[" netlist:term "]" : tactic => do
  withMainContext do
    let expression ← instantiateMVars (← Term.elabTerm netlist none)
    match expression.getAppFn.constName? with
    | some name => SpiceSolveTactic.run name
    | none => throwErrorAt netlist
        "spice_solve: expected a loaded netlist constant"

end LeanModels.Spice
