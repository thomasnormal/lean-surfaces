import LeanModels.Cpp

open LeanModels.Cpp

private def report (label : String) (result : Except String α)
    (describe : α → String) : IO Unit := do
  match result with
  | .ok value => IO.println s!"{label}: OK {describe value}"
  | .error error => IO.println s!"{label}: REFUSE {error}"

private def parsePath (text : String) : Except String (List Nat) := do
  if text == "root" then return []
  (text.splitOn ".").mapM fun part =>
    match part.toNat? with
    | some index => pure index
    | none => .error s!"invalid occurrence path: {text}"

private def inspect (probe : DeclarationProbe) (paths : List (List Nat)) : IO UInt32 := do
  let artifact : Artifact := {
    sourceFile := "", sourceSha256 := "", frontend := .object [], dependencies := []
    ast := probe.ast }
  let declarations := artifact.declarations
  IO.println "Probe inspection and source-local forms; no artifact provenance, literal compilation or execution admission."
  IO.println s!"metadata={probe.declarations.length} occurrences={declarations.length} functions={probe.functions.length}"
  report "type-evidence" (parseValidatedTypeEvidence probe)
    (fun rows => s!"{rows.length} validated rows")
  for path in paths do
    let some declaration := declarations.find? (fun declaration => declaration.path == path)
      | IO.eprintln s!"missing declaration occurrence at {repr path}"; return 1
    IO.println s!"path={repr path} kind={declaration.kind}"
    report "canonical-target" (canonicalTargetCandidates artifact probe declaration)
      (fun targets => toString targets.length)
    report "canonical-root" (canonicalRootEvidence probe declaration) (fun _ => "present")
    report "canonical-chain" (canonicalPredecessorChainEvidence probe declaration)
      (fun chain => toString chain.length)
    report "semantic-chain" (semanticContextChainEvidence artifact probe declaration)
      (fun chain => toString chain.length)
    report "lexical-chain" (lexicalContextChainEvidence artifact probe declaration)
      (fun chain => toString chain.length)
    report "function-definition" (functionDefinitionEvidence probe declaration) toString
    report "local-function" (admitLocalFunctionDeclaration probe path)
      (fun admitted => s!"defines={admitted.form.definesEntity} parameters={admitted.parameters.length}")
    report "linkage" (linkageEvidence probe declaration)
      (fun evidence => s!"{evidence.internal}/{evidence.formal}/{evidence.language}")
  return 0

private def censusLocalFunctions (probe : DeclarationProbe) : IO UInt32 := do
  let artifact : Artifact := {
    sourceFile := "", sourceSha256 := "", frontend := .object [], dependencies := []
    ast := probe.ast }
  let occurrences := artifact.declarations.filter (fun declaration => declaration.kind == "FunctionDecl")
  let mut admitted := 0
  let mut definitions := 0
  let mut refusals : List (String × Nat) := []
  for occurrence in occurrences do
    match admitLocalFunctionDeclaration probe occurrence.path with
    | .ok declaration =>
        admitted := admitted + 1
        if declaration.form.definesEntity then definitions := definitions + 1
        IO.println s!"path={repr occurrence.path} name={occurrence.name} defines={declaration.form.definesEntity}"
    | .error error =>
        if refusals.any (fun refusal => refusal.1 == error) then
          refusals := refusals.map (fun refusal =>
            if refusal.1 == error then (error, refusal.2 + 1) else refusal)
        else refusals := refusals ++ [(error, 1)]
  IO.println s!"local-function occurrences={occurrences.length} admitted={admitted} definitions={definitions} refused={occurrences.length - admitted}"
  for (error, count) in refusals do IO.println s!"refused={count} reason={error}"
  IO.println "Source-local classification only; no entity relation, provenance or execution admission."
  return 0

def main (arguments : List String) : IO UInt32 := do
  let input :: selections := arguments
    | IO.eprintln "usage: lake env lean --run extractors/cpp/inspect_probe.lean PROBE [--local-functions|root|INDEX.INDEX ...]"; return 1
  let census := selections == ["--local-functions"]
  let paths ← match (if census then [] else selections).mapM parsePath with
    | .ok paths => pure paths
    | .error error => IO.eprintln error; return 1
  let bytes ← IO.FS.readBinFile input
  let some contents := String.fromUTF8? bytes
    | IO.eprintln "probe: invalid UTF-8"; return 1
  let probe ← match parseDeclarationProbeString contents with
    | .ok probe => pure probe
    | .error error => IO.eprintln s!"probe: {error}"; return 1
  if census then censusLocalFunctions probe else inspect probe paths
