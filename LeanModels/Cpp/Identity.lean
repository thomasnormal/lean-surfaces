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

end LeanModels.Cpp
