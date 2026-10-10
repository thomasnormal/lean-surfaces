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
  IO.println "Probe observations only; no artifact provenance, literal compilation or execution admission."
  IO.println s!"metadata={probe.declarations.length} occurrences={declarations.length} functions={probe.functions.length}"
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
    report "linkage" (linkageEvidence probe declaration)
      (fun evidence => s!"{evidence.internal}/{evidence.formal}/{evidence.language}")
  return 0

def main (arguments : List String) : IO UInt32 := do
  let input :: selections := arguments
    | IO.eprintln "usage: lake env lean --run extractors/cpp/inspect_probe.lean PROBE [root|INDEX.INDEX ...]"; return 1
  let paths ← match selections.mapM parsePath with
    | .ok paths => pure paths
    | .error error => IO.eprintln error; return 1
  let bytes ← IO.FS.readBinFile input
  let some contents := String.fromUTF8? bytes
    | IO.eprintln "probe: invalid UTF-8"; return 1
  let probe ← match parseDeclarationProbeString contents with
    | .ok probe => pure probe
    | .error error => IO.eprintln s!"probe: {error}"; return 1
  inspect probe paths
