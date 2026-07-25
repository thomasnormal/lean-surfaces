import LeanModels.VerilogA.Elaboration
import Mathlib.Tactic

/-!
# Verilog-A contribution proof surface

`load_veriloga` reads a `.va` source and its generated `.json` companion.
OpenVAF Reloaded owns preprocessing and parsing; Lean verifies the envelope
matches the source byte-for-byte, decodes its normalized AST projection,
elaborates typed IDs, and emits a kernel-checked structural-validity theorem.
-/

namespace LeanModels.VerilogA

open LeanModels.Circuit

initialize verilogAPortTables :
    Lean.EnvExtension (Lean.NameMap (Array String)) ←
  Lean.registerEnvExtension (pure {})

initialize verilogAParameterTables :
    Lean.EnvExtension (Lean.NameMap (Array String)) ←
  Lean.registerEnvExtension (pure {})

structure SourceProvenance where
  path : String
  envelopePath : String
  hash : UInt64
  frontendRevision : String

initialize verilogAProvenanceTables :
    Lean.EnvExtension (Lean.NameMap SourceProvenance) ←
  Lean.registerEnvExtension (pure {})

deriving instance Lean.ToExpr for Span
deriving instance Lean.ToExpr for SourceBranch
deriving instance Lean.ToExpr for SourceExpr
deriving instance Lean.ToExpr for SourceTarget
deriving instance Lean.ToExpr for SourceContribution
deriving instance Lean.ToExpr for SourceParameter
deriving instance Lean.ToExpr for SourceModule
deriving instance Lean.ToExpr for FrontendProvenance
deriving instance Lean.ToExpr for SourceArtifact
deriving instance Lean.ToExpr for Envelope
deriving instance Lean.ToExpr for PortId
deriving instance Lean.ToExpr for ParameterId
deriving instance Lean.ToExpr for ElectricalBranch
deriving instance Lean.ToExpr for ContributionExpr
deriving instance Lean.ToExpr for ContributionTarget
deriving instance Lean.ToExpr for Contribution
deriving instance Lean.ToExpr for ContributionModel

open Lean Elab Command in
elab "load_veriloga " name:ident " from " path:str : command => do
  let pathString := path.getString
  let sourcePath : System.FilePath := ⟨pathString⟩
  let envelopePath := sourcePath.withExtension "json"
  let envelopePathString := envelopePath.toString
  let sourceText ←
    match ← (IO.FS.readFile ⟨pathString⟩).toBaseIO with
    | .ok contents => pure contents
    | .error error =>
        throwErrorAt path
          "load_veriloga: cannot read '{pathString}': {toString error}"
  let envelopeText ←
    match ← (IO.FS.readFile envelopePath).toBaseIO with
    | .ok contents => pure contents
    | .error error =>
        throwErrorAt path
          "load_veriloga: cannot read generated OpenVAF envelope \
          '{envelopePathString}': {toString error}; run \
          `python3 extractors/veriloga/extract.py {pathString}`"
  let envelope ← match parseEnvelopeString envelopeText with
    | .ok envelope => pure envelope
    | .error error =>
        throwErrorAt path "load_veriloga: {error}"
  unless envelope.source.path == pathString do
    throwErrorAt path
      "load_veriloga: envelope source path is \
      '{envelope.source.path}', want '{pathString}'; regenerate it"
  unless envelope.source.text == sourceText do
    throwErrorAt path
      "load_veriloga: '{pathString}' has changed since OpenVAF extraction; \
      run `python3 extractors/veriloga/extract.py {pathString}`"
  let model ← match elaborate envelope.module with
    | .ok model => pure model
    | .error error =>
        throwErrorAt path "load_veriloga: {error.describe}"
  let declarationName := (← getCurrNamespace) ++ name.getId
  if (← getEnv).contains declarationName then
    throwErrorAt name
      "load_veriloga: '{declarationName}' has already been declared"
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
      value := Lean.toExpr sourceText
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst (companionName "_source_text")
    addAndCompile <| .defnDecl {
      name := companionName "_source_hash"
      levelParams := []
      type := Lean.mkConst ``UInt64
      value := Lean.toExpr (hash sourceText)
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst (companionName "_source_hash")
    addAndCompile <| .defnDecl {
      name := companionName "_source"
      levelParams := []
      type := Lean.mkConst ``SourceModule
      value := Lean.toExpr envelope.module
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst (companionName "_source")
    addAndCompile <| .defnDecl {
      name := declarationName
      levelParams := []
      type := Lean.mkConst ``ContributionModel
      value := Lean.toExpr model
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst declarationName
  modifyEnv fun environment =>
    verilogAPortTables.modifyState environment fun tables =>
      tables.insert declarationName model.portNames
  modifyEnv fun environment =>
    verilogAParameterTables.modifyState environment fun tables =>
      tables.insert declarationName model.parameterNames
  modifyEnv fun environment =>
    verilogAProvenanceTables.modifyState environment fun tables =>
      tables.insert declarationName
        ⟨pathString, envelopePathString, hash sourceText,
          envelope.frontend.revision⟩
  let modelId := mkIdent declarationName
  let theoremId :=
    mkIdent (.mkSimple (declarationName.getString! ++ "_valid"))
  elabCommand (← `(theorem $theoremId :
      ContributionModel.Valid $modelId := by
        norm_num [ContributionModel.Valid, ContributionTarget.validFor,
          ContributionExpr.validFor, ElectricalBranch.validFor,
          $(modelId):term]
        all_goals
          intro contribution hcontribution
          simp_all))
  liftTermElabM do
    Term.addTermInfo' name (Lean.mkConst declarationName)
      (isBinder := true)

syntax:max "va_port! " term:max str : term
syntax:max "va_parameter! " term:max str : term
syntax:max "va_branch! " term:max str str : term

open Lean Elab Term in
private def loadedModelName (modelSyntax : Syntax)
    (command : String) : TermElabM Name := do
  let modelExpr ← elabTerm modelSyntax
    (some (mkConst ``ContributionModel))
  match modelExpr.getAppFn.constName? with
  | some modelName => pure modelName
  | none =>
      throwErrorAt modelSyntax
        "{command}: expected a model constant introduced by `load_veriloga`"

open Lean Elab Term in
elab_rules : term
  | `(va_port! $model:term $name:str) => do
      let modelName ← loadedModelName model "va_port!"
      let tables := verilogAPortTables.getState (← getEnv)
      let names ← match tables.find? modelName with
        | some names => pure names
        | none => throwErrorAt model
            "va_port!: no port table is registered for `{modelName}`"
      match names.findIdx? (· == name.getString.toLower) with
      | some index =>
          elabTerm (← `(PortId.mk $(quote index))) none
      | none => throwErrorAt name
          "va_port!: `{name.getString}` is not a port of the loaded model"

open Lean Elab Term in
elab_rules : term
  | `(va_parameter! $model:term $name:str) => do
      let modelName ← loadedModelName model "va_parameter!"
      let tables := verilogAParameterTables.getState (← getEnv)
      let names ← match tables.find? modelName with
        | some names => pure names
        | none => throwErrorAt model
            "va_parameter!: no parameter table is registered for `{modelName}`"
      match names.findIdx? (· == name.getString.toLower) with
      | some index =>
          elabTerm (← `(ParameterId.mk $(quote index))) none
      | none => throwErrorAt name
          "va_parameter!: `{name.getString}` is not a parameter of the loaded model"

open Lean Elab Term in
elab_rules : term
  | `(va_branch! $model:term $positive:str $negative:str) => do
      let modelName ← loadedModelName model "va_branch!"
      let tables := verilogAPortTables.getState (← getEnv)
      let names ← match tables.find? modelName with
        | some names => pure names
        | none => throwErrorAt model
            "va_branch!: no port table is registered for `{modelName}`"
      let positiveIndex ← match
          names.findIdx? (· == positive.getString.toLower) with
        | some index => pure index
        | none => throwErrorAt positive
            "va_branch!: `{positive.getString}` is not a port"
      let negativeIndex ← match
          names.findIdx? (· == negative.getString.toLower) with
        | some index => pure index
        | none => throwErrorAt negative
            "va_branch!: `{negative.getString}` is not a port"
      elabTerm
        (← `(ElectricalBranch.mk
          (PortId.mk $(quote positiveIndex))
          (PortId.mk $(quote negativeIndex))))
        none

end LeanModels.VerilogA
