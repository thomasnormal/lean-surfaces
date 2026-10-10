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

end LeanModels.Cpp
