import LeanModels.Circuit.Contribution
import LeanModels.VerilogA.Envelope

/-!
# Typed elaboration of the minimal Verilog-A subset

Port and parameter names are resolved exactly once. The resulting
`ContributionModel` contains only numeric IDs and typed electrical branches.
-/

namespace LeanModels.VerilogA

open LeanModels.Circuit

inductive ElaborationError where
  | duplicatePort (name : String)
  | duplicateParameter (name : String)
  | portDeclarationsDiffer
  | missingPort (span : Span) (name : String)
  | missingParameter (span : Span) (name : String)
  | unsupportedDdt (span : Span)
  | emptyContributions
deriving Repr, BEq, Inhabited

def ElaborationError.describe : ElaborationError → String
  | .duplicatePort name => s!"duplicate Verilog-A port `{name}`"
  | .duplicateParameter name =>
      s!"duplicate Verilog-A parameter `{name}`"
  | .portDeclarationsDiffer =>
      "`module`, `inout`, and `electrical` port declarations must agree"
  | .missingPort span name =>
      s!"line {span.line}: unknown Verilog-A electrical port `{name}`"
  | .missingParameter span name =>
      s!"line {span.line}: unknown Verilog-A parameter `{name}`"
  | .unsupportedDdt span =>
      s!"line {span.line}: only `ddt(V(port, port))` is supported"
  | .emptyContributions =>
      "Verilog-A module has no analog contribution statements"

private def firstDuplicate? (names : Array String) : Option String := Id.run do
  for (name, index) in names.zipIdx do
    if names.take index |>.contains name then return some name
  return none

private def resolvePort (source : SourceModule) (span : Span)
    (name : String) : Except ElaborationError PortId :=
  match source.ports.findIdx? (· == name) with
  | some index => pure ⟨index⟩
  | none => throw (.missingPort span name)

private def resolveBranch (source : SourceModule) (span : Span)
    (branch : SourceBranch) : Except ElaborationError ElectricalBranch := do
  pure {
    positive := ← resolvePort source span branch.positive
    negative := ← resolvePort source span branch.negative }

private def resolveParameter (source : SourceModule) (span : Span)
    (name : String) : Except ElaborationError ParameterId :=
  match source.parameters.findIdx? (·.name == name) with
  | some index => pure ⟨index⟩
  | none => throw (.missingParameter span name)

private def elaborateExpr (source : SourceModule) (span : Span) :
    SourceExpr → Except ElaborationError ContributionExpr
  | .literal value => pure (.literal value)
  | .name name => do
      pure (.parameter (← resolveParameter source span name))
  | .potential branch => do
      pure (.potential (← resolveBranch source span branch))
  | .flow branch => do
      pure (.flow (← resolveBranch source span branch))
  | .ddt (.potential branch) => do
      pure (.potentialRate (← resolveBranch source span branch))
  | .ddt _ => throw (.unsupportedDdt span)
  | .neg value => do
      pure (.neg (← elaborateExpr source span value))
  | .add left right => do
      pure (.add
        (← elaborateExpr source span left)
        (← elaborateExpr source span right))
  | .sub left right => do
      pure (.sub
        (← elaborateExpr source span left)
        (← elaborateExpr source span right))
  | .mul left right => do
      pure (.mul
        (← elaborateExpr source span left)
        (← elaborateExpr source span right))
  | .div left right => do
      pure (.div
        (← elaborateExpr source span left)
        (← elaborateExpr source span right))

private def elaborateTarget (source : SourceModule) (span : Span) :
    SourceTarget → Except ElaborationError ContributionTarget
  | .potential branch => do
      pure (.potential (← resolveBranch source span branch))
  | .flow branch => do
      pure (.flow (← resolveBranch source span branch))

def elaborate (source : SourceModule) :
    Except ElaborationError ContributionModel := do
  if let some duplicate := firstDuplicate? source.ports then
    throw (.duplicatePort duplicate)
  unless source.inouts == source.ports &&
      source.electricals == source.ports do
    throw .portDeclarationsDiffer
  let parameterNames := source.parameters.map (·.name)
  if let some duplicate := firstDuplicate? parameterNames then
    throw (.duplicateParameter duplicate)
  if source.contributions.isEmpty then
    throw .emptyContributions
  let mut contributions := #[]
  for contribution in source.contributions do
    contributions := contributions.push {
      target := ← elaborateTarget source contribution.span
        contribution.target
      expression := ← elaborateExpr source contribution.span
        contribution.expression }
  pure {
    name := source.name
    portNames := source.ports
    parameterNames
    parameterDefaults := source.parameters.map (·.defaultValue)
    contributions }

def decodeAndElaborate (envelope : String) :
    Except String ContributionModel := do
  let parsed ← parseEnvelopeString envelope
  elaborate parsed.module |>.mapError (·.describe)

end LeanModels.VerilogA
