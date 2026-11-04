import Lean
import LeanModels.Circuit.ExactLiteral
import LeanModels.VerilogA.Ast

/-!
# OpenVAF AST envelope ingestion

The source parser is OpenVAF Reloaded, pinned by repository and revision in
the envelope. This module performs no Verilog-A parsing. It only decodes the
deterministic projection produced by `extractors/veriloga/extract.py` and
converts exact literal token text to `Rat`.
-/

namespace LeanModels.VerilogA

open Lean (Json)
open LeanModels.Circuit

def openVafRepository : String :=
  "https://github.com/OpenVAF/OpenVAF-Reloaded"

def openVafRevision : String :=
  "b4517adc0a21ef42e03b396373553a41174444c4"

def envelopeSchema : String :=
  "lean-models.veriloga.openvaf-ast.v1"

private def withCtx (context : String) :
    Except String α → Except String α
  | .ok value => .ok value
  | .error message => .error s!"{context}: {message}"

private def getField (json : Json) (name : String) :
    Except String Json :=
  withCtx s!"field {name.quote}" (json.getObjVal? name)

private def getString (json : Json) (name : String) :
    Except String String := do
  withCtx s!"field {name.quote}" ((← getField json name).getStr?)

private def parseStringArray (json : Json) :
    Except String (Array String) := do
  (← json.getArr?).mapM (·.getStr?)

private def parseBranch (json : Json) :
    Except String SourceBranch := do
  pure {
    positive := ← getString json "positive"
    negative := ← getString json "negative" }

mutual
  partial def parseExpr (json : Json) :
      Except String SourceExpr := withCtx "expression" do
    let kind ← getString json "kind"
    match kind with
    | "literal" =>
        let token ← getString json "text"
        match ExactLiteral.parse token with
        | some value => pure (.literal value)
        | none => throw s!"unsupported exact numeric literal {token.quote}"
    | "name" => pure (.name (← getString json "name"))
    | "potential" =>
        pure (.potential (← parseBranch json))
    | "flow" =>
        pure (.flow (← parseBranch json))
    | "ddt" =>
        pure (.ddt (← parseExpr (← getField json "value")))
    | "neg" =>
        pure (.neg (← parseExpr (← getField json "value")))
    | "add" =>
        pure (.add
          (← parseExpr (← getField json "left"))
          (← parseExpr (← getField json "right")))
    | "sub" =>
        pure (.sub
          (← parseExpr (← getField json "left"))
          (← parseExpr (← getField json "right")))
    | "mul" =>
        pure (.mul
          (← parseExpr (← getField json "left"))
          (← parseExpr (← getField json "right")))
    | "div" =>
        pure (.div
          (← parseExpr (← getField json "left"))
          (← parseExpr (← getField json "right")))
    | other =>
        throw s!"unknown OpenVAF expression projection {other.quote}"
end

private def parseTarget (json : Json) :
    Except String SourceTarget := withCtx "target" do
  let kind ← getString json "kind"
  match kind with
  | "potential" => pure (.potential (← parseBranch json))
  | "flow" => pure (.flow (← parseBranch json))
  | other => throw s!"unknown contribution target {other.quote}"

private def parseParameter (json : Json) :
    Except String SourceParameter := withCtx "parameter" do
  let token ← getString json "default"
  let defaultValue ←
    match ExactLiteral.parse token with
    | some value => pure value
    | none => throw s!"unsupported exact parameter default {token.quote}"
  pure {
    span := ⟨0, 0⟩
    name := ← getString json "name"
    defaultValue }

private def parseContribution (json : Json) :
    Except String SourceContribution := withCtx "contribution" do
  pure {
    span := ⟨0, 0⟩
    target := ← parseTarget (← getField json "target")
    expression := ← parseExpr (← getField json "expression") }

private def parseModule (json : Json) :
    Except String SourceModule := withCtx "module" do
  pure {
    span := ⟨0, 0⟩
    name := ← getString json "name"
    ports := ← parseStringArray (← getField json "ports")
    inouts := ← parseStringArray (← getField json "inouts")
    electricals := ← parseStringArray (← getField json "electricals")
    parameters :=
      ← (← (← getField json "parameters").getArr?).mapM parseParameter
    contributions :=
      ← (← (← getField json "contributions").getArr?).mapM
        parseContribution }

def parseEnvelope (json : Json) : Except String Envelope :=
  withCtx "Verilog-A envelope" do
    let schema ← getString json "schema"
    unless schema == envelopeSchema do
      throw s!"unsupported schema {schema.quote}; want {envelopeSchema.quote}"
    let frontendJson ← getField json "frontend"
    let frontend : FrontendProvenance := {
      name := ← getString frontendJson "name"
      repository := ← getString frontendJson "repository"
      revision := ← getString frontendJson "revision"
      representation := ← getString frontendJson "representation" }
    unless frontend.name == "OpenVAF Reloaded" do
      throw s!"unsupported Verilog-A frontend {frontend.name.quote}"
    unless frontend.repository == openVafRepository do
      throw s!"unexpected OpenVAF repository {frontend.repository.quote}"
    unless frontend.revision == openVafRevision do
      throw s!"unexpected OpenVAF revision {frontend.revision.quote}"
    let sourceJson ← getField json "source"
    pure {
      schema
      frontend
      source := {
        path := ← getString sourceJson "path"
        text := ← getString sourceJson "text" }
      module := ← parseModule (← getField json "module") }

def parseEnvelopeString (text : String) :
    Except String Envelope :=
  Json.parse text >>= parseEnvelope

end LeanModels.VerilogA
