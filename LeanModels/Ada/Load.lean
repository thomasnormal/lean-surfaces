import LeanModels.Ada.Json

/-!
# `load_ada_program` — elaboration-time envelope ingestion (`LeanModels.Ada`)

The Ada lane's analogue of `load_c_program` and the Python lane's
`load_program`: read an `ada-0.1` envelope at ELABORATION time and define it
as a **literal** first-order term, so `#guard`s (and later, proofs) can
unfold it.

    load_ada_program report from "Examples/ada/report/report.json"

Missing files, malformed envelopes, a wrong `language` and a wrong
`schema_version` are all clear elaboration errors, never silent.

## Two things are REFUSED, and neither is a stamp

* **`profile_id`**, for `load_c_program`'s reason: the profile is an INPUT
  to the AST, so an envelope extracted under another profile is a different
  program.
* **`language_version`**, which is Ada's own and is not optional. The ARM is
  Ada 2022 and the official suite is ACATS 4.2, an Ada 2012 suite — the
  version pair is FORCED (`docs/ada-charter.md` §1.3). Annex J is a whole
  annex of obsolescent features, so "the same source under a different
  edition" is a real difference and not a hypothetical.

## The vocabulary is READ, not restated

`docs/ada-envelope-schema.md` §3 makes `docs/ada-construct-census.json`'s
`node_kinds` the single source of truth for what the ingester accepts, and
refuses to copy the 280 kinds into any second place. This command honours
that literally: it reads the census file at elaboration time and passes the
set to the parser. **The Lean side therefore cannot drift from the census
without the build failing**, which is the same-set gate the schema promised,
enforced by the ingester rather than only by a harness.
-/

namespace LeanModels.Ada

deriving instance Lean.ToExpr for AdaSpan
deriving instance Lean.ToExpr for Node
deriving instance Lean.ToExpr for SourceFile
deriving instance Lean.ToExpr for CompilationUnit
deriving instance Lean.ToExpr for Marking
deriving instance Lean.ToExpr for Diagnostic
deriving instance Lean.ToExpr for Envelope

/-- The schema this ingester accepts. -/
def acceptedSchema : String := "ada-0.1"

/-- The profile this ingester accepts. A mismatch is refused, not stamped. -/
def acceptedProfile : String := "ada-profile-0.1"

/-- Where the accepted vocabulary lives. Not a copy — the file
`harness/ada_construct_census.py` writes. -/
def vocabPath : String := "docs/ada-construct-census.json"

open Lean Elab Command in
/--
`load_ada_program e from "path.json"` reads the `ada-0.1` envelope at
elaboration time and defines `e : Envelope` as a literal term — the whole
envelope, not just its units, because `markings` (the expected result of
37.1% of the ACATS) and `source_files` are claims the ingester must be
checkable against too.

Paths resolve against the current working directory — the package root under
`lake build`.
-/
elab "load_ada_program " name:ident " from " path:str : command => do
  let pathStr := path.getString
  let vocabRaw ←
    match ← (IO.FS.readFile ⟨vocabPath⟩).toBaseIO with
    | .ok c => pure c
    | .error e =>
        throwErrorAt path
          "load_ada_program: cannot read the census '{vocabPath}': {toString e}\nIt is the single source of truth for the accepted node vocabulary (docs/ada-envelope-schema.md §3) and is produced by `harness/ada_construct_census.py`. (Relative paths resolve against the current working directory — the package root under `lake build`; current cwd: '{toString (← IO.currentDir)}')"
  let vocab ←
    match parseVocabString vocabRaw with
    | .error e => throwErrorAt path "load_ada_program: '{vocabPath}' is not a usable census: {e}"
    | .ok v => pure v
  let contents ←
    match ← (IO.FS.readFile ⟨pathStr⟩).toBaseIO with
    | .ok c => pure c
    | .error e =>
        throwErrorAt path
          "load_ada_program: cannot read '{pathStr}': {toString e}\n(relative paths resolve against the current working directory — the package root under `lake build`; current cwd: '{toString (← IO.currentDir)}')"
  let envl ←
    match parseEnvelopeString vocab contents with
    | .error e =>
        throwErrorAt path "load_ada_program: '{pathStr}' is not a valid ada-0.1 envelope: {e}"
    | .ok envl => pure envl
  unless envl.language == "ada" do
    throwErrorAt path
      "load_ada_program: '{pathStr}' has language '{envl.language}', expected 'ada'"
  unless envl.schemaVersion == acceptedSchema do
    throwErrorAt path
      "load_ada_program: '{pathStr}' is schema '{envl.schemaVersion}', but this ingester pins '{acceptedSchema}'"
  unless envl.profileId == acceptedProfile do
    throwErrorAt path
      "load_ada_program: '{pathStr}' was extracted under profile '{envl.profileId}', but this ingester pins '{acceptedProfile}'. The profile is an INPUT to the AST, not a stamp on it — an envelope from another profile is a different program (docs/ada-envelope-schema.md §0.1)."
  let declName := (← getCurrNamespace) ++ name.getId
  if (← getEnv).contains declName then
    throwErrorAt name "load_ada_program: '{declName}' has already been declared"
  liftCoreM do
    addAndCompile <| .defnDecl {
      name := declName
      levelParams := []
      type := Lean.mkConst ``LeanModels.Ada.Envelope
      value := Lean.toExpr envl
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst declName
    addDocStringCore declName
      s!"Ada envelope loaded by `load_ada_program` from `{pathStr}` (edition `{envl.languageVersion}`, profile `{envl.profileId}`, {envl.sourceFiles.size} source file(s), {envl.compilationUnits.size} compilation unit(s)). A literal `LeanModels.Ada.Envelope`."
  liftTermElabM do
    Term.addTermInfo' name (Lean.mkConst declName) (isBinder := true)

end LeanModels.Ada
