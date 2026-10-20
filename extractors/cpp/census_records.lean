import LeanModels.Cpp

open LeanModels.Cpp Lean

/- Runtime integral-record schema admission of complete probes. This is never a
function-admission, literal-compilation or method-execution claim. The external
launch receipt must pin the inputs, compiler and budgets. -/

private def jsonObject := Json.mkObj

private def counts (values : List String) : Json :=
  jsonObject (values.eraseDups.map fun value =>
    (value, toJson (values.count value)))

private def physicalFile (raw : Raw) : Except String (Option String) := do
  match raw with
  | .null => pure none
  | _ =>
      let file ← evidenceText raw "file"
      unless !file.isEmpty do throw "source origin: empty file"
      let _ ← evidenceNat raw "offset"
      pure (some file)

private def origin (probe : DeclarationProbe) (declaration : LeanModels.Cpp.Declaration) :
    Except String (Option String × Option String × Bool) := do
  let rows := probe.declarations.filter (·.id.value == declaration.id)
  let row :: rest := rows | throw "source origin: missing declaration metadata"
  requireEvidenceText row.raw "source_origin_api"
    "SourceManager expansion/spelling file locations v1"
  let raw ← evidenceField row.raw "source_origin"
  unless row.kind == declaration.kind && rest.all (fun other =>
      other.kind == row.kind && other.implicit == row.implicit &&
      other.raw.field "source_origin_api" == row.raw.field "source_origin_api" &&
      other.raw.field "source_origin" == some raw) do
    throw "source origin: conflicting declaration metadata"
  let expansion ← physicalFile (← evidenceField raw "expansion")
  let spelling ← physicalFile (← evidenceField raw "spelling")
  pure (expansion, spelling, row.implicit)

private def canonicalFile (file : Option String) : IO (Option String) := do
  match file with
  | none => pure none
  | some file =>
      try return some (← IO.FS.realPath file).toString
      catch _ => return none

private def ownership (sources : List String)
    (expansion spelling : Option String) : String :=
  match expansion, spelling with
  | some expansion, some spelling =>
      if sources.contains expansion && sources.contains spelling then "target-source"
      else if sources.contains expansion || sources.contains spelling then "mixed-macro"
      else "dependency"
  | _, _ => "unknown-origin"

private def emit (value : Json) : IO Unit := IO.println value.compress

private def refuse (stage error : String) : IO UInt32 := do
  emit (jsonObject [("format", toJson "cpp-record-schema-census-1"),
    ("status", toJson "REFUSE"), ("stage", toJson stage), ("reason", toJson error),
    ("execution", toJson "not-attempted")])
  return 2

private def progress (message : String) : IO Unit := do
  let output ← IO.getStderr
  output.putStrLn message
  output.flush

private def census (probe : DeclarationProbe) (sources : List String) : IO UInt32 := do
  progress "validating whole-probe type evidence"
  let types ← match parseValidatedTypeEvidence probe with
    | .ok rows => pure rows
    | .error error => return ← refuse "type-evidence" error
  let artifact : LeanModels.Cpp.Artifact := {
    sourceFile := "", sourceSha256 := "", frontend := Raw.null
    dependencies := [], ast := probe.ast }
  let candidates := artifact.declarations.filter (fun declaration =>
    declaration.kind == "CXXRecordDecl" &&
      ((probe.ast.atPath declaration.path).bind (fun raw => raw.field "completeDefinition")) == some (.bool true))
  let mut reports : List Json := []
  let mut groups : List String := []
  let mut targetRefusals : List String := []
  let mut targetAdmitted := 0
  let mut targetExplicit := 0
  progress s!"classifying {candidates.length} complete record definition occurrences"
  for declaration in candidates do
    let (expansion, spelling, implicit) ← match origin probe declaration with
      | .ok value => pure value
      | .error error => return ← refuse "source-origin" error
    let expansion ← canonicalFile expansion
    let spelling ← canonicalFile spelling
    let group := ownership sources expansion spelling
    groups := group :: groups
    let result := admitIntegralRecordSchemaWithTypes probe types declaration.path
    if group == "target-source" && !implicit then
      targetExplicit := targetExplicit + 1
      match result with
      | .ok _ => targetAdmitted := targetAdmitted + 1
      | .error error => targetRefusals := error :: targetRefusals
    reports := jsonObject [
      ("path", toJson declaration.path), ("occurrence", toJson declaration.id),
      ("name", toJson declaration.name), ("implicit", toJson implicit),
      ("ownership", toJson group), ("expansion_file", toJson expansion),
      ("spelling_file", toJson spelling), ("admitted", toJson result.isOk),
      ("field_count", toJson (result.toOption.map (fun schema => schema.fields.length))),
      ("first_refusal", toJson (match result with
        | .ok _ => (none : Option String) | .error error => some error))] :: reports
  emit (jsonObject [
    ("format", toJson "cpp-record-schema-census-1"), ("status", toJson "COMPLETE"),
    ("scope", toJson "runtime-integral-record-schema-admission"),
    ("execution", toJson "not-attempted"), ("literal_compilation", toJson "not-attempted"),
    ("ownership_basis", toJson "physical declared-name expansion and spelling files; both must be selected"),
    ("counting_basis", toJson "retained complete CXXRecordDecl occurrences; no deduplication"),
    ("refusal_basis", toJson "first semantic refusal per record schema"),
    ("type_rows", toJson types.length), ("definition_occurrences", toJson candidates.length),
    ("ownership_counts", counts groups), ("target_explicit_records", toJson targetExplicit),
    ("target_explicit_admitted", toJson targetAdmitted),
    ("target_explicit_refused", toJson targetRefusals.length),
    ("target_first_refusals", counts targetRefusals), ("records", toJson reports.reverse)])
  return 0

def main (arguments : List String) : IO UInt32 := do
  let input :: "--sources" :: sources := arguments
    | IO.eprintln "usage: lake env lean --run extractors/cpp/census_records.lean PROBE --sources FILE ..."; return 1
  if sources.isEmpty then IO.eprintln "select at least one source file"; return 1
  try
    let sources ← sources.mapM fun source => do
      let file ← IO.FS.realPath (System.FilePath.mk source)
      unless (← file.metadata).type == .file do
        throw (IO.userError "selected source is not a file")
      pure file.toString
    -- Bound before reading/decoding. Resource rejection is not semantic refusal.
    let before ← (System.FilePath.mk input).metadata
    unless before.type == .file do
      return ← refuse "input-io" "probe must be a regular file"
    if before.byteSize > 128 * 1024 * 1024 then
      return ← refuse "input-byte-bound" "probe exceeds 128 MiB runtime census bound"
    let bytes ← IO.FS.readBinFile input
    let after ← (System.FilePath.mk input).metadata
    unless before.byteSize == after.byteSize && before.modified == after.modified &&
        after.byteSize.toNat == bytes.size do
      return ← refuse "input-read" "probe changed while reading"
    let some contents := String.fromUTF8? bytes
      | return ← refuse "probe-format" "invalid UTF-8"
    progress "parsing complete probe"
    let probe ← match parseDeclarationProbeString contents with
      | .ok probe => pure probe
      | .error error => return ← refuse "probe-format" error
    census probe sources
  catch error => refuse "input-io" error.toString
