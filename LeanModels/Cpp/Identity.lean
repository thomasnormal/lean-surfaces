import LeanModels.Cpp.Ast
import LeanModels.Cpp.Evidence

namespace LeanModels.Cpp

def canonicalTargetCandidates (artifact : Artifact) (probe : DeclarationProbe)
    (declaration : Declaration) : Except String (List Declaration) :=
  let rows := probe.declarations.filter fun row => row.id.value == declaration.id
  match rows with
  | [] => .error "canonical evidence missing for declaration occurrence"
  | row :: rest =>
      if row.kind != declaration.kind then
        .error "canonical evidence kind disagrees with declaration occurrence"
      else if rest.any (fun other => other.kind != row.kind) then
        .error "canonical evidence rows disagree on declaration kind"
      else if rest.any (fun other => other.canonical.value != row.canonical.value) then
        .error "canonical evidence rows disagree on canonical target"
      else
        let candidates := artifact.declarationsById row.canonical.value
        if candidates.isEmpty then
          .error "canonical target is absent from artifact"
        else
          .ok candidates

def canonicalRootEvidence (probe : DeclarationProbe) (declaration : Declaration) :
    Except String FrontendHandle :=
  let rows := probe.declarations.filter fun row => row.id.value == declaration.id
  match rows with
  | [] => .error "canonical evidence missing for declaration occurrence"
  | row :: rest =>
      if row.kind != declaration.kind then
        .error "canonical evidence kind disagrees with declaration occurrence"
      else if rest.any (fun other =>
          other.kind != row.kind || other.canonical.value != row.canonical.value ||
            other.previous != row.previous) then
        .error "canonical evidence rows disagree on root relation"
      else
        let roots := probe.declarations.filter fun other => other.id.value == row.canonical.value
        match roots with
        | [] => .error "canonical root evidence is absent"
        | root :: rootRest =>
            if root.kind != row.kind || root.canonical.value != root.id.value then
              .error "canonical root evidence is not idempotent"
            else if root.previous.isSome || rootRest.any (fun other =>
                other.kind != root.kind || other.canonical.value != root.canonical.value ||
                  other.previous.isSome) then
              .error "canonical root must have an explicit null predecessor"
            else if row.id.value != root.id.value && row.previous.isNone then
              .error "nonroot canonical evidence requires a predecessor"
            else
              .ok root.id

def canonicalPredecessorChainEvidence (probe : DeclarationProbe) (declaration : Declaration) :
    Except String (List FrontendHandle) :=
  go (probe.declarations.length + 1) [] declaration.id none []
where
  go (fuel : Nat) (active : List String) (current : String)
      (expectedRoot : Option String) (chain : List FrontendHandle) :
      Except String (List FrontendHandle) :=
    match fuel with
    | 0 => .error "canonical predecessor chain exceeds artifact bound"
    | fuel + 1 =>
        if active.contains current then
          .error "canonical predecessor chain contains a cycle"
        else
          let rows := probe.declarations.filter fun row => row.id.value == current
          match rows with
          | [] => .error "canonical predecessor target is absent"
          | row :: rest =>
              if row.kind != declaration.kind then
                .error "canonical predecessor kind disagrees with source declaration"
              else if rest.any (fun other =>
                  other.kind != row.kind || other.canonical.value != row.canonical.value ||
                    other.previous != row.previous) then
                .error "canonical predecessor rows disagree"
              else if expectedRoot.any (· != row.canonical.value) then
                .error "canonical predecessor rows disagree on canonical root"
              else
                let chain := chain ++ [row.id]
                match row.previous with
                | some previous =>
                    go fuel (current :: active) previous.value (some row.canonical.value) chain
                | none =>
                    if row.canonical.value != row.id.value then
                      .error "canonical predecessor chain ends before its root"
                    else
                      .ok chain

def functionDefinitionEvidence (probe : DeclarationProbe) (declaration : Declaration) :
    Except String Bool :=
  let rows := probe.declarations.filter fun row => row.id.value == declaration.id
  match rows with
  | [] => .error "function-definition evidence missing for declaration occurrence"
  | row :: rest =>
      if declaration.kind != "FunctionDecl" || row.kind != "FunctionDecl" then
        .error "function-definition evidence requires FunctionDecl"
      else
        match row.functionShape with
        | none => .error "function-definition shape evidence missing"
        | some shape =>
            if rest.any (fun other => other.kind != row.kind) then
              .error "function-definition evidence rows disagree on declaration kind"
            else if rest.any (fun other => other.functionShape != some shape) then
              .error "function-definition evidence rows disagree on local shape"
            else
              .ok shape.definition

def contextTargetCandidates (artifact : Artifact) (probe : DeclarationProbe)
    (declaration : Declaration) (semantic : Bool) : Except String (List Declaration) :=
  let rows := probe.declarations.filter fun row => row.id.value == declaration.id
  match rows with
  | [] => .error "context evidence missing for declaration occurrence"
  | row :: rest =>
      let target := if semantic then row.semanticContext else row.lexicalContext
      if row.kind != declaration.kind then
        .error "context evidence kind disagrees with declaration occurrence"
      else if rest.any (fun other =>
          other.kind != row.kind ||
            (if semantic then other.semanticContext else other.lexicalContext) != target) then
        .error "context evidence rows disagree on target"
      else
        match target with
        | none => .ok []
        | some handle =>
            let candidates := artifact.declarationsById handle.value
            if candidates.isEmpty then
              .error "context target is absent from artifact"
            else
              .ok candidates

def semanticContextCandidates (artifact : Artifact) (probe : DeclarationProbe)
    (declaration : Declaration) : Except String (List Declaration) :=
  contextTargetCandidates artifact probe declaration true

def lexicalContextCandidates (artifact : Artifact) (probe : DeclarationProbe)
    (declaration : Declaration) : Except String (List Declaration) :=
  contextTargetCandidates artifact probe declaration false

def contextChainEvidence (artifact : Artifact) (probe : DeclarationProbe)
    (declaration : Declaration) (semantic : Bool) : Except String (List FrontendHandle) :=
  let fuel := probe.declarations.length + 1
  go fuel [] declaration.id []
where
  go (fuel : Nat) (active : List String) (current : String)
      (chain : List FrontendHandle) : Except String (List FrontendHandle) :=
    match fuel with
    | 0 => .error "context chain exceeds artifact bound"
    | fuel + 1 =>
        if active.contains current then
          .error "context chain contains a cycle"
        else if (artifact.declarationsById current).isEmpty then
          .error "context chain target is absent from artifact"
        else
          let rows := probe.declarations.filter fun row => row.id.value == current
          match rows with
          | [] => .error "context chain row is absent from metadata"
          | row :: rest =>
              let target := if semantic then row.semanticContext else row.lexicalContext
              if rest.any (fun other =>
                  other.kind != row.kind ||
                    (if semantic then other.semanticContext else other.lexicalContext) != target) then
                .error "context chain rows disagree"
              else
                let chain := if current == declaration.id then chain else chain ++ [row.id]
                if row.kind == "TranslationUnitDecl" then
                  match target with
                  | none => .ok chain
                  | some _ => .error "translation-unit context must be null"
                else
                  match target with
                  | none => .error "nonroot context must have a parent"
                  | some parent => go fuel (current :: active) parent.value chain

def semanticContextChainEvidence (artifact : Artifact) (probe : DeclarationProbe)
    (declaration : Declaration) : Except String (List FrontendHandle) :=
  contextChainEvidence artifact probe declaration true

def lexicalContextChainEvidence (artifact : Artifact) (probe : DeclarationProbe)
    (declaration : Declaration) : Except String (List FrontendHandle) :=
  contextChainEvidence artifact probe declaration false

structure LinkageEvidence where
  internal : String
  formal : String
  language : Option String
  deriving Repr, BEq, Inhabited, Lean.ToExpr

def linkageNames : List String :=
  ["Invalid", "None", "Internal", "UniqueExternal", "VisibleNone", "Module", "External"]

def languageLinkageNames : List String := ["C", "C++", "None"]

def linkageText (raw : Raw) (name : String) (allowed : List String) : Except String String := do
  let value ← evidenceText raw name
  unless allowed.contains value do
    throw s!"unsupported linkage value for {name}: {value}"
  return value

def linkageLanguage (raw : Raw) (kind : String) : Except String (Option String) := do
  if kind == "FunctionDecl" || kind == "VarDecl" then
    return some (← linkageText raw "language_linkage" languageLinkageNames)
  match raw.field "language_linkage" with
  | none => return none
  | some (.string value) =>
      unless languageLinkageNames.contains value do
        throw s!"unsupported linkage value for language_linkage: {value}"
      return some value
  | some _ => throw "evidence field language_linkage: expected string"

def linkageObservation (row : DeclarationEvidenceRow) : Except String LinkageEvidence := do
  let internal ← linkageText row.raw "linkage_internal" linkageNames
  let formal ← linkageText row.raw "linkage_formal" linkageNames
  let language ← linkageLanguage row.raw row.kind
  return {internal, formal, language}

def linkageEvidence (probe : DeclarationProbe) (declaration : Declaration) :
    Except String LinkageEvidence :=
  if declaration.kind == "TranslationUnitDecl" then
    .error "linkage evidence is not applicable to TranslationUnitDecl"
  else
    let rows := probe.declarations.filter fun row => row.id.value == declaration.id
    match rows with
    | [] => .error "linkage evidence missing for declaration occurrence"
    | row :: rest =>
        if row.kind != declaration.kind then
          .error "linkage evidence kind disagrees with declaration occurrence"
        else
          match linkageObservation row with
          | .error error => .error error
          | .ok observation =>
              if rest.any (fun other => other.kind != row.kind) then
                .error "linkage evidence rows disagree on declaration kind"
              else
                match rest.mapM linkageObservation with
                | .error error => .error error
                | .ok observations =>
                    if observations.any (fun other => other != observation) then
                      .error "linkage evidence rows disagree on observed values"
                    else
                      .ok observation

end LeanModels.Cpp
