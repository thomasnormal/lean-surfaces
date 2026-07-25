import LeanModels.Circuit.Block
import LeanModels.Circuit.AC
import LeanModels.Circuit.Assurance
import LeanModels.Spice.Mos1Resolved
import Mathlib.Tactic
import Lean.Util.CollectAxioms

/-!
# Circuit proof surface

`load_circuit` parses SPICE directly in Lean and elaborates it to one typed,
analysis-independent circuit artifact. For the supported linear subset it
also emits a proof-carrying exact DC view and a checked exact solution.
-/

namespace LeanModels.Circuit

initialize circuitNodeTables :
    Lean.EnvExtension (Lean.NameMap (Array String)) ←
  Lean.registerEnvExtension (pure {})

initialize circuitDeviceTables :
    Lean.EnvExtension (Lean.NameMap (Array String)) ←
  Lean.registerEnvExtension (pure {})

initialize circuitSourceTables :
    Lean.EnvExtension (Lean.NameMap Spice.SourceCircuit) ←
  Lean.registerEnvExtension (pure {})

structure CircuitSourceProvenance where
  path : String
  hash : UInt64

initialize circuitProvenanceTables :
    Lean.EnvExtension (Lean.NameMap CircuitSourceProvenance) ←
  Lean.registerEnvExtension (pure {})

deriving instance Lean.ToExpr for Dimension
deriving instance Lean.ToExpr for NatureDecl
deriving instance Lean.ToExpr for DisciplineDecl
deriving instance Lean.ToExpr for NodeId
deriving instance Lean.ToExpr for DeviceId
deriving instance Lean.ToExpr for ModelId
deriving instance Lean.ToExpr for DCDevice
deriving instance Lean.ToExpr for DCCircuit
deriving instance Lean.ToExpr for ElaboratedDevice
deriving instance Lean.ToExpr for MosPolarity
deriving instance Lean.ToExpr for ElaboratedMos1Model
deriving instance Lean.ToExpr for ElaboratedModel
deriving instance Lean.ToExpr for ElaboratedCircuit
deriving instance Lean.ToExpr for DCBlock
deriving instance Lean.ToExpr for DCSolution
deriving instance Lean.ToExpr for Spice.SourceSpan
deriving instance Lean.ToExpr for Spice.SourceDeviceKind
deriving instance Lean.ToExpr for Spice.SourceDevice
deriving instance Lean.ToExpr for Spice.SourceMosPolarity
deriving instance Lean.ToExpr for Spice.SourceMosModel
deriving instance Lean.ToExpr for Spice.SourceMosfet
deriving instance Lean.ToExpr for Spice.SourceInstance
deriving instance Lean.ToExpr for Spice.SourceSubcircuit
deriving instance Lean.ToExpr for Spice.SourceCircuit
deriving instance Lean.ToExpr for LeanModels.Spice.NodeId
deriving instance Lean.ToExpr for LeanModels.Spice.SourceId
deriving instance Lean.ToExpr for LeanModels.Spice.TransistorId
deriving instance Lean.ToExpr for LeanModels.Spice.ModelId
deriving instance Lean.ToExpr for LeanModels.Spice.Mos1Model
deriving instance Lean.ToExpr for LeanModels.Spice.Mos1VoltageSource
deriving instance Lean.ToExpr for LeanModels.Spice.Mos1Transistor
deriving instance Lean.ToExpr for LeanModels.Spice.Mos1Device
deriving instance Lean.ToExpr for LeanModels.Spice.Mos1ResolvedCircuit

open Lean Elab Command in
elab "load_circuit_source " name:ident " from " path:str : command => do
  let pathString := path.getString
  let contents ←
    match ← (IO.FS.readFile ⟨pathString⟩).toBaseIO with
    | .ok contents => pure contents
    | .error error =>
        throwErrorAt path
          "load_circuit_source: cannot read '{pathString}': {toString error}"
  let source ← match Spice.parse contents with
    | .ok source => pure source
    | .error error =>
        throwErrorAt path "load_circuit_source: {error.describe}"
  let declarationName := (← getCurrNamespace) ++ name.getId
  if (← getEnv).contains declarationName then
    throwErrorAt name
      "load_circuit_source: '{declarationName}' has already been declared"
  liftCoreM do
    addAndCompile <| .defnDecl {
      name := declarationName
      levelParams := []
      type := Lean.mkConst ``Spice.SourceCircuit
      value := Lean.toExpr source
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst declarationName
  modifyEnv fun environment =>
    circuitSourceTables.modifyState environment fun tables =>
      tables.insert declarationName source
  modifyEnv fun environment =>
    circuitProvenanceTables.modifyState environment fun tables =>
      tables.insert declarationName ⟨pathString, hash contents⟩

open Lean Elab Command in
elab "load_circuit " name:ident " from " path:str : command => do
  let pathString := path.getString
  let contents ←
    match ← (IO.FS.readFile ⟨pathString⟩).toBaseIO with
    | .ok contents => pure contents
    | .error error =>
        throwErrorAt path
          "load_circuit: cannot read '{pathString}': {toString error}"
  let source ← match Spice.parse contents with
    | .ok source => pure source
    | .error error =>
        throwErrorAt path "load_circuit: {error.describe}"
  let circuit ← match Spice.elaborate source with
    | .ok circuit => pure circuit
    | .error error =>
        throwErrorAt path "load_circuit: {error.describe}"
  let exactResult :=
    match circuit.toDCCircuit with
    | .ok dc =>
        match solveDC dc with
        | .ok solution => some (dc, solution)
        | .error _ => none
    | .error _ => none
  let mos1Result := LeanModels.Spice.sharedToMos1Circuit circuit
  let declarationName := (← getCurrNamespace) ++ name.getId
  if (← getEnv).contains declarationName then
    throwErrorAt name
      "load_circuit: '{declarationName}' has already been declared"
  let companionName (suffix : String) : Name :=
    .str declarationName.getPrefix (declarationName.getString! ++ suffix)
  liftCoreM do
    addAndCompile <| .defnDecl {
      name := companionName "_source_path"
      levelParams := []
      type := Lean.mkConst ``String
      value := Lean.toExpr pathString
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst (companionName "_source_path")
    addAndCompile <| .defnDecl {
      name := companionName "_source_text"
      levelParams := []
      type := Lean.mkConst ``String
      value := Lean.toExpr contents
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst (companionName "_source_text")
    addAndCompile <| .defnDecl {
      name := companionName "_source_hash"
      levelParams := []
      type := Lean.mkConst ``UInt64
      value := Lean.toExpr (hash contents)
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst (companionName "_source_hash")
    addAndCompile <| .defnDecl {
      name := companionName "_source"
      levelParams := []
      type := Lean.mkConst ``Spice.SourceCircuit
      value := Lean.toExpr source
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst (companionName "_source")
    addAndCompile <| .defnDecl {
      name := declarationName
      levelParams := []
      type := Lean.mkConst ``ElaboratedCircuit
      value := Lean.toExpr circuit
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst declarationName
    if let some (dc, solution) := exactResult then
      addAndCompile <| .defnDecl {
        name := companionName "_dc"
        levelParams := []
        type := Lean.mkConst ``DCCircuit
        value := Lean.toExpr dc
        hints := .abbrev
        safety := .safe }
      enableRealizationsForConst (companionName "_dc")
      addAndCompile <| .defnDecl {
        name := companionName "_solution"
        levelParams := []
        type := Lean.mkConst ``DCSolution
        value := Lean.toExpr solution
        hints := .abbrev
        safety := .safe }
      enableRealizationsForConst (companionName "_solution")
    if let .ok mos1 := mos1Result then
      addAndCompile <| .defnDecl {
        name := companionName "_mos1"
        levelParams := []
        type := Lean.mkConst ``LeanModels.Spice.Mos1ResolvedCircuit
        value := Lean.toExpr mos1
        hints := .abbrev
        safety := .safe }
      enableRealizationsForConst (companionName "_mos1")
  modifyEnv fun environment =>
    circuitNodeTables.modifyState environment fun tables =>
      tables.insert declarationName circuit.nodeNames
  modifyEnv fun environment =>
    circuitDeviceTables.modifyState environment fun tables =>
      tables.insert declarationName circuit.deviceNames
  modifyEnv fun environment =>
    circuitSourceTables.modifyState environment fun tables =>
      tables.insert declarationName source
  modifyEnv fun environment =>
    circuitProvenanceTables.modifyState environment fun tables =>
      tables.insert declarationName ⟨pathString, hash contents⟩
  let circuitId := mkIdent declarationName
  if exactResult.isSome then
    let dcId := mkIdent (companionName "_dc")
    let solutionId := mkIdent (companionName "_solution")
    let projectionId :=
      mkIdent (.mkSimple (declarationName.getString! ++ "_dc_projection"))
    let viewId :=
      mkIdent (.mkSimple (declarationName.getString! ++ "_exact_dc"))
    let theoremId :=
      mkIdent (.mkSimple (declarationName.getString! ++ "_solution_satisfies"))
    elabCommand (← `(theorem $projectionId :
        ElaboratedCircuit.toDCCircuit $circuitId = .ok $dcId := by
          rfl))
    elabCommand (← `(abbrev $viewId :
        ExactDCView $circuitId where
        dc := $dcId
        projected := $projectionId))
    elabCommand (← `(attribute [instance] $viewId))
    elabCommand (← `(theorem $theoremId :
        DCSatisfies $dcId ($solutionId).assignment := by
          unfold $dcId $solutionId
          norm_num [DCSatisfies, dcSatisfiesBool, DCSolution.assignment,
            DCCircuit.isValid, DCCircuit.nodes, DCCircuit.kcl, DCDevice.lawHolds,
            DCDevice.positive, DCDevice.negative, DCDevice.id,
            DCDevice.currentLeaving, DCAssignment.voltage,
            DCAssignment.current]
          all_goals
            intro index hindex
            interval_cases index <;>
              norm_num [DCDevice.positive, DCDevice.negative, DCDevice.id,
                DCDevice.currentLeaving]))
  if mos1Result.isOk then
    let mos1Id := mkIdent (companionName "_mos1")
    let circuitTerm : Term := ⟨circuitId.raw⟩
    let mos1Term : Term := ⟨mos1Id.raw⟩
    let projectionId :=
      mkIdent (.mkSimple (declarationName.getString! ++ "_mos1_projection"))
    let viewId :=
      mkIdent (.mkSimple (declarationName.getString! ++ "_mos1_view"))
    elabCommand (← `(theorem $projectionId :
        LeanModels.Spice.sharedToMos1Circuit $circuitId = .ok $mos1Id := by
          norm_num [LeanModels.Spice.sharedToMos1Circuit,
            LeanModels.Spice.sharedDevice, LeanModels.Spice.sharedModel,
            LeanModels.Spice.sharedNode, $circuitTerm:term, $mos1Term:term]
          rfl))
    elabCommand (← `(abbrev $viewId :
        LeanModels.Spice.Mos1View $circuitId where
        mos1 := $mos1Id
        projected := $projectionId))
    elabCommand (← `(attribute [instance] $viewId))
  liftTermElabM do
    Term.addTermInfo' name (Lean.mkConst declarationName) (isBinder := true)

/- Close a concrete circuit equation by kernel definitional equality while
allowing reduction through opaque executable definitions. This is intended
for large source-layout certificates where `simp` would materialize an
enormous intermediate term. The resulting proof term is only `Eq.refl`. -/
open Lean Elab Tactic Meta in
elab "circuit_reduce" : tactic => do
  let goal ← getMainGoal
  goal.withContext do
    let target ← instantiateMVars (← goal.getType)
    let some (_, lhs, _) := target.eq?
      | throwError
          "circuit_reduce: expected an equality goal:{indentExpr target}"
    let proof ← mkEqRefl lhs
    withTransparency .all do
      unless ← isDefEq (← inferType proof) target do
        throwError
          "circuit_reduce: equality is not definitionally true:{indentExpr target}"
      goal.assign proof
  replaceMainGoal []

syntax:max "node! " term:max str : term
syntax:max "circuit_node! " term:max str : term
syntax:max "device! " term:max str : term
syntax:max "subcircuit! " term:max str : term

open Lean Elab Term in
elab_rules : term
  | `(node! $circuit:term $name:str) => do
      let circuitExpr ← elabTerm circuit (some (mkConst ``ElaboratedCircuit))
      let circuitName ← match circuitExpr.getAppFn.constName? with
        | some circuitName => pure circuitName
        | none =>
            throwErrorAt circuit
              "node!: expected a circuit constant introduced by `load_circuit`"
      let tables := circuitNodeTables.getState (← getEnv)
      let names ← match tables.find? circuitName with
        | some names => pure names
        | none =>
            throwErrorAt circuit
              "node!: no node table is registered for `{circuitName}`"
      match names.findIdx? (· == name.getString.toLower) with
      | some index =>
        let indexSyntax := quote index
        elabTerm
          (← `(ElaboratedNode.mk (circuit := $circuit)
            ⟨$indexSyntax⟩ (by decide)))
          none
      | none =>
        throwErrorAt name
          "node!: `{name.getString}` is not present in the loaded circuit"

open Lean Elab Term in
elab_rules : term
  | `(circuit_node! $circuit:term $name:str) => do
      let circuitExpr ← elabTerm circuit (some (mkConst ``ElaboratedCircuit))
      let circuitName ← match circuitExpr.getAppFn.constName? with
        | some circuitName => pure circuitName
        | none =>
            throwErrorAt circuit
              "circuit_node!: expected a circuit constant introduced by `load_circuit`"
      let tables := circuitNodeTables.getState (← getEnv)
      let names ← match tables.find? circuitName with
        | some names => pure names
        | none =>
            throwErrorAt circuit
              "circuit_node!: no node table is registered for `{circuitName}`"
      match names.findIdx? (· == name.getString.toLower) with
      | some index =>
        let indexSyntax := quote index
        elabTerm
          (← `(ElaboratedNode.mk (circuit := $circuit)
            ⟨$indexSyntax⟩ (by decide)))
          none
      | none =>
        throwErrorAt name
          "circuit_node!: `{name.getString}` is not present in the loaded circuit"

open Lean Elab Term in
elab_rules : term
  | `(device! $circuit:term $name:str) => do
      let circuitExpr ← elabTerm circuit (some (mkConst ``ElaboratedCircuit))
      let circuitName ← match circuitExpr.getAppFn.constName? with
        | some circuitName => pure circuitName
        | none =>
            throwErrorAt circuit
              "device!: expected a circuit constant introduced by `load_circuit`"
      let tables := circuitDeviceTables.getState (← getEnv)
      let names ← match tables.find? circuitName with
        | some names => pure names
        | none =>
            throwErrorAt circuit
              "device!: no device table is registered for `{circuitName}`"
      match names.findIdx? (· == name.getString.toLower) with
      | some index =>
        let indexSyntax := quote index
        elabTerm
          (← `(ElaboratedDeviceRef.mk (circuit := $circuit)
            ⟨$indexSyntax⟩ (by decide)))
          none
      | none =>
        throwErrorAt name
          "device!: `{name.getString}` is not present in the loaded circuit"

open Lean Elab Term in
elab_rules : term
  | `(subcircuit! $circuit:term $name:str) => do
      let circuitExpr ← elabTerm circuit (some (mkConst ``ElaboratedCircuit))
      let circuitName ← match circuitExpr.getAppFn.constName? with
        | some circuitName => pure circuitName
        | none =>
            throwErrorAt circuit
              "subcircuit!: expected a circuit constant introduced by `load_circuit`"
      let tables := circuitSourceTables.getState (← getEnv)
      let source ← match tables.find? circuitName with
        | some source => pure source
        | none =>
            throwErrorAt circuit
              "subcircuit!: no source hierarchy is registered for `{circuitName}`"
      let subcircuitName := name.getString.toLower
      let subcircuit ←
        match source.subcircuits.find? (·.name == subcircuitName) with
        | some subcircuit => pure subcircuit
        | none =>
            throwErrorAt name
              "subcircuit!: `{name.getString}` is not defined in the loaded circuit"
      let block ← match subcircuit.toDCBlock with
        | .ok block => pure block
        | .error error => throwErrorAt name "subcircuit!: {error}"
      return Lean.toExpr block

syntax:50 term:51 " ⊨dc " "{" ident ", " ident " => " term "}" : term
macro_rules
  | `($circuit ⊨dc { $voltage, $current => $property }) =>
      `(DCModels $circuit (fun $voltage $current => $property))

macro "#circuit_check " circuit:term " dc" : command =>
  `(#guard (solveCircuitDC $circuit).isOk)

macro "#circuit_check " circuit:term " dc" " shows "
    node:str " = " expected:term : command =>
  `(#guard
    match solveCircuitDC $circuit with
    | Except.ok solution =>
        solution.assignment.observeVoltage $circuit
          (node! $circuit $node) == $expected
    | Except.error _ => false)

namespace CircuitDCTactic

open Lean Elab Tactic

private def companionName (base : Name) (suffix : String) : Name :=
  .str base.getPrefix (base.getString! ++ suffix)

private def baseFromGoal : TacticM Name := withMainContext do
  let target := (← instantiateMVars (← getMainTarget)).cleanupAnnotations
  let circuit ←
    if target.isAppOfArity ``DCModels 3 then pure (target.getArg! 0)
    else if target.isAppOfArity ``RealizableDC 2 then pure (target.getArg! 0)
    else if target.isAppOfArity ``DeterminateDC 2 then pure (target.getArg! 0)
    else
      throwError
        "circuit_dc: expected a `⊨dc`, `RealizableDC`, or `DeterminateDC` goal"
  match circuit.getAppFn.constName? with
  | some name => pure name
  | none =>
      throwError
        "circuit_dc: the goal's circuit is not a `load_circuit` constant"

private def run (base : Name) : TacticM Unit := do
  let circuit : Term := ⟨(mkIdent base).raw⟩
  let solutionName := companionName base "_solution"
  let satisfiesName := companionName base "_solution_satisfies"
  let dcName := companionName base "_dc"
  let viewName :=
    .mkSimple (base.getString! ++ "_exact_dc")
  unless (← getEnv).contains solutionName && (← getEnv).contains satisfiesName do
    throwError
      "circuit_dc: `{base}` has no checked exact solution companions"
  let solution : Term := ⟨(mkIdent solutionName).raw⟩
  let satisfies : Term := ⟨(mkIdent satisfiesName).raw⟩
  let dcTerm : Term := ⟨(mkIdent dcName).raw⟩
  let viewTerm : Term := ⟨(mkIdent viewName).raw⟩
  let target := (← instantiateMVars (← getMainTarget)).cleanupAnnotations
  if target.isAppOfArity ``RealizableDC 2 then
    evalTactic
      (← `(tactic| exact ⟨($solution:term).assignment, $satisfies:term⟩))
  else if target.isAppOfArity ``DeterminateDC 2 then
    let nodeTables := circuitNodeTables.getState (← getEnv)
    let nodeNames := (nodeTables.find? base).getD #[]
    let deviceTables := circuitDeviceTables.getState (← getEnv)
    let deviceNames := (deviceTables.find? base).getD #[]
    evalTactic (← `(tactic| (
      intro left right hleft hright
      change DCSatisfies $dcTerm:term left at hleft
      change DCSatisfies $dcTerm:term right at hright
      rcases left with ⟨leftVoltages, leftCurrents⟩
      rcases right with ⟨rightVoltages, rightCurrents⟩
      unfold DCSatisfies dcSatisfiesBool at hleft hright
      simp [DCCircuit.isValid, DCCircuit.nodes, DCCircuit.kcl,
        DCDevice.lawHolds, DCDevice.currentLeaving,
        DCAssignment.voltage, DCAssignment.current,
        DCDevice.positive, DCDevice.negative, DCDevice.id,
        $viewTerm:term, $dcTerm:term] at hleft hright)))
    for index in List.range nodeNames.size do
      if nodeNames[index]! != "0" then
        let leftHypothesis := mkIdent (.mkSimple s!"hleftKcl{index}")
        let rightHypothesis := mkIdent (.mkSimple s!"hrightKcl{index}")
        let indexSyntax := quote index
        evalTactic (← `(tactic| (
          have $leftHypothesis:ident := hleft.2 $indexSyntax (by omega)
          have $rightHypothesis:ident := hright.2 $indexSyntax (by omega)
          simp at $leftHypothesis:ident $rightHypothesis:ident)))
    let nodeCount := quote nodeNames.size
    let deviceCount := quote deviceNames.size
    evalTactic (← `(tactic| (
      rw [DCAssignment.mk.injEq]
      constructor
      · apply Array.ext
        · exact hleft.1.1.1.1.trans hright.1.1.1.1.symm
        · intro index hindexLeft hindexRight
          have hindex : index < $nodeCount := by omega
          interval_cases index <;> simp_all <;> grind
      · apply Array.ext
        · exact hleft.1.1.1.2.trans hright.1.1.1.2.symm
        · intro index hindexLeft hindexRight
          have hindex : index < $deviceCount := by omega
          interval_cases index <;> simp_all <;> grind)))
  else
    evalTactic (← `(tactic| (
      intro assignment hphysical
      change DCSatisfies $dcTerm:term assignment at hphysical
      unfold DCSatisfies at hphysical
      unfold dcSatisfiesBool at hphysical
      simp [DCCircuit.nodes, DCCircuit.kcl, DCDevice.currentLeaving,
        DCCircuit.isValid, DCDevice.lawHolds,
        DCAssignment.voltage, DCAssignment.current,
        DCAssignment.observeVoltage, DCAssignment.observeCurrent,
        $viewTerm:term, $dcTerm:term, $circuit:term] at hphysical ⊢
      norm_num at hphysical ⊢)))
    let tables := circuitNodeTables.getState (← getEnv)
    let names := (tables.find? base).getD #[]
    for index in List.range names.size do
      if names[index]! != "0" then
        let hypothesis := mkIdent (.mkSimple s!"hkcl{index}")
        let indexSyntax := quote index
        evalTactic (← `(tactic| (
          have $hypothesis:ident := hphysical.2 $indexSyntax (by norm_num)
          norm_num [DCDevice.positive, DCDevice.negative, DCDevice.id,
            DCDevice.currentLeaving] at $hypothesis:ident)))
    evalTactic (← `(tactic| grind))

end CircuitDCTactic

open Lean Elab Tactic in
elab "circuit_dc" : tactic => do
  CircuitDCTactic.run (← CircuitDCTactic.baseFromGoal)

/-! ## Checked assurance reports -/

private inductive AssuranceCategory where
  | universal
  | realizable
  | determinate
  | domain
  | linearization
  | validity
  | other
deriving BEq

private def assuranceCategory (type : Lean.Expr) : AssuranceCategory :=
  let rec result (expression : Lean.Expr) : Lean.Expr :=
    match expression with
    | .forallE _ _ body _ => result body
    | _ => expression
  match (result type).getAppFn.constName? with
  | some ``DCModels | some ``SafeUnder => .universal
  | some ``RealizableDC | some ``RealizableUnder => .realizable
  | some ``DeterminateDC | some ``DeterminateUnder => .determinate
  | some ``StaysWithinValidityDomain => .domain
  | some ``ExactLinearizationAt => .linearization
  | some ``AcceptedValidity => .validity
  | _ => .other

private def AssuranceCategory.label : AssuranceCategory → String
  | .universal => "universal"
  | .realizable => "realizable"
  | .determinate => "determinate"
  | .domain => "domain-closure"
  | .linearization => "linearization"
  | .validity => "physical-validity"
  | .other => "supporting"

private def standardAxiom (name : Lean.Name) : Bool :=
  name == ``propext ||
  name == ``Classical.choice ||
  name == ``Quot.sound

private def declarationResultType : Lean.Expr → Lean.Expr
  | .forallE _ _ body _ => declarationResultType body
  | expression => expression

private def checkedAxiomText {m : Type → Type} [Monad m] [Lean.MonadEnv m]
    (declaration : Lean.Name) : m (Except String String) := do
  let axioms ← Lean.collectAxioms declaration
  pure <| do
    if axioms.contains ``sorryAx then
      throw s!"`{declaration}` depends on `sorryAx`"
    let nonstandard := axioms.filter fun axiomName =>
      !standardAxiom axiomName
    unless nonstandard.isEmpty do
      throw s!"`{declaration}` has nonstandard axioms: {nonstandard}"
    if axioms.isEmpty then pure "none"
    else pure (String.intercalate ", " (axioms.toList.map toString))

syntax (name := circuitAssuranceReport)
  "#assurance_report " term:max " using " ident " [" ident,* "]" : command

open Lean Elab Command in
elab_rules : command
  | `(#assurance_report $circuit:term using $assurance:ident
      [$declarations:ident,*]) => do
      let circuitExpr ← liftTermElabM <|
        Term.elabTerm circuit (some (mkConst ``ElaboratedCircuit))
      let circuitName ← match circuitExpr.getAppFn.constName? with
        | some name => pure name
        | none =>
            throwErrorAt circuit
              "#assurance_report: expected a `load_circuit` constant"
      let provenance ←
        match (circuitProvenanceTables.getState (← getEnv)).find?
            circuitName with
        | some provenance => pure provenance
        | none =>
            throwErrorAt circuit
              "#assurance_report: no source provenance for `{circuitName}`"
      let source ←
        match (circuitSourceTables.getState (← getEnv)).find? circuitName with
        | some source => pure source
        | none =>
            throwErrorAt circuit
              "#assurance_report: no checked hierarchy for `{circuitName}`"
      let assuranceName ← liftCoreM <|
        Lean.Elab.realizeGlobalConstNoOverloadWithInfo assurance
      let assuranceInfo ← match (← getEnv).find? assuranceName with
        | some info => pure info
        | none =>
            throwErrorAt assurance
              "#assurance_report: unknown assurance case `{assuranceName}`"
      let assuranceType := declarationResultType assuranceInfo.type
      unless assuranceType.getAppFn.constName? == some ``AssuranceCase do
        throwErrorAt assurance
          "#assurance_report: `{assuranceName}` is not an `AssuranceCase`; \
          safety, realizability, and domain closure must be bundled over the \
          same behavior and allowed-world predicate"
      let assuranceArguments := assuranceType.getAppArgs
      unless assuranceArguments.size == 10 do
        throwErrorAt assurance
          "#assurance_report: malformed `AssuranceCase` type for \
          `{assuranceName}`"
      let assuredCircuit := assuranceArguments[4]!
      let circuitMatches ← liftTermElabM do
        Meta.isDefEq circuitExpr assuredCircuit
      unless circuitMatches do
        throwErrorAt assurance
          "#assurance_report: `{assuranceName}` is attached to a different \
          elaborated circuit"
      let assuranceAxioms ←
        match ← checkedAxiomText assuranceName with
        | .ok text => pure text
        | .error error => throwErrorAt assurance "#assurance_report: {error}"
      let mut rows : Array String := #[]
      let mut hasValidity := false
      for declaration in declarations.getElems do
        let name ← liftCoreM <|
          Lean.Elab.realizeGlobalConstNoOverloadWithInfo declaration
        let info ← match (← getEnv).find? name with
          | some info => pure info
          | none => throwErrorAt declaration "unknown declaration `{name}`"
        let category := assuranceCategory info.type
        if category == .validity then
          hasValidity := true
        let axiomText ←
          match ← checkedAxiomText name with
          | .ok text => pure text
          | .error error =>
              throwErrorAt declaration "#assurance_report: {error}"
        rows := rows.push
          s!"  {name}: {category.label}; axioms=[{axiomText}]"
      let validity :=
        if hasValidity then "accepted claim included"
        else "MISSING (model-level theorem only; no physical coverage evidence)"
      let hierarchy :=
        s!"{source.subcircuits.size} subcircuits, {source.instances.size} top-level instances"
      logInfo m!"Assurance report for {circuitName}
  source: {provenance.path}
  source hash: {provenance.hash}
  frontend: direct Lean SPICE parser; hierarchy checked ({hierarchy})
  model validity: {validity}
  {assuranceName}: source-bound typed assurance case; checked projection + safety + realizability + domain closure; axioms=[{assuranceAxioms}]
{String.intercalate "\n" rows.toList}
  external simulators: validation only; never theorem premises"

end LeanModels.Circuit
