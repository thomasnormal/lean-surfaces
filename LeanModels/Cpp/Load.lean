import LeanModels.Cpp.Json
import LeanModels.Cpp.Evidence

namespace LeanModels.Cpp

open Lean Elab Command in
elab "load_cpp_artifact " name:ident " from " path:str : command => do
  let contents ← IO.FS.readFile ⟨path.getString⟩
  let artifact ← match parseArtifactString contents with
    | .ok artifact => pure artifact
    | .error error => throwErrorAt path "load_cpp_artifact: {error}"
  let declarationName := (← getCurrNamespace) ++ name.getId
  if (← getEnv).contains declarationName then
    throwErrorAt name "load_cpp_artifact: '{declarationName}' already declared"
  liftCoreM do
    addAndCompile <| .defnDecl {
      name := declarationName, levelParams := []
      type := Lean.mkConst ``LeanModels.Cpp.Artifact
      value := Lean.toExpr artifact, hints := .abbrev, safety := .safe }
    enableRealizationsForConst declarationName
    addDocStringCore declarationName
      s!"Literal Clang translation artifact from {artifact.sourceFile}; sha256 {artifact.sourceSha256}. No execution admission."
  liftTermElabM do
    Term.addTermInfo' name (Lean.mkConst declarationName) (isBinder := true)

open Lean Elab Command in
elab "load_cpp_probe " name:ident " from " path:str : command => do
  let contents ← IO.FS.readFile ⟨path.getString⟩
  let probe ← match parseDeclarationProbeString contents with
    | .ok probe => pure probe
    | .error error => throwErrorAt path "load_cpp_probe: {error}"
  let declarationName := (← getCurrNamespace) ++ name.getId
  if (← getEnv).contains declarationName then
    throwErrorAt name "load_cpp_probe: '{declarationName}' already declared"
  liftCoreM do
    addAndCompile <| .defnDecl {
      name := declarationName, levelParams := []
      type := Lean.mkConst ``LeanModels.Cpp.DeclarationProbe
      value := Lean.toExpr probe, hints := .abbrev, safety := .safe }
    enableRealizationsForConst declarationName
    addDocStringCore declarationName
      "Literal versioned Clang frontend observations; no process-provenance, semantic or execution admission."
  liftTermElabM do
    Term.addTermInfo' name (Lean.mkConst declarationName) (isBinder := true)

end LeanModels.Cpp
