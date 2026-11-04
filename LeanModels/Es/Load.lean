import LeanModels.Es.Json

/-!
# `load_es_program` — elaboration-time envelope ingestion (`LeanModels.Es`)

The ECMAScript lane's analogue of `load_program` and `load_c_program`:
read an `es-0.2` envelope at ELABORATION time and define it as a
**literal** first-order term, so `#guard`s (and later, proofs) can unfold
it.

    load_es_program myFile from "Examples/es/.../file.json"

Missing files, malformed envelopes, a wrong `schema_version` and a wrong
`language_version` are all clear elaboration errors, never silent. The
edition is REFUSED on mismatch: unlike a frontend stamp it is an INPUT to
the AST (`docs/es-envelope-schema.md` §0(1)), because the grammar a parser
accepts is a function of the edition — 106 of the core slice's tests parse
under the living draft and not under a ratified edition. An envelope from
another edition is a different program.

A source that did NOT parse loads fine, as a `ParseResult.error`. That is
the point: 4,248 of the language-core slice's tests assert exactly that.
-/

namespace LeanModels.Es

deriving instance Lean.ToExpr for EsSpan
deriving instance Lean.ToExpr for NodeKind
deriving instance Lean.ToExpr for Lit
deriving instance Lean.ToExpr for Scalar
deriving instance Lean.ToExpr for Node
deriving instance Lean.ToExpr for ParseResult
deriving instance Lean.ToExpr for SourceType
deriving instance Lean.ToExpr for Envelope

/-- The schema this ingester reads. -/
def acceptedSchema : String := "es-0.2"

/-- The edition this tier claims. The same string that names
`LeanModels/Es/ES2026/` and that `docs/es-edition.json` pins, so path,
envelope and citation cannot drift. -/
def acceptedEdition : String := "ES2026"

open Lean Elab Command in
/--
`load_es_program e from "path.json"` reads the `es-0.2` envelope at
elaboration time and defines `e : Envelope` as a literal term.
The path resolves against the current working directory — the package
root under `lake build`.
-/
elab "load_es_program " name:ident " from " path:str : command => do
  let pathStr := path.getString
  let contents ←
    match ← (IO.FS.readFile ⟨pathStr⟩).toBaseIO with
    | .ok c => pure c
    | .error e =>
        throwErrorAt path
          "load_es_program: cannot read '{pathStr}': {toString e}\n(relative paths resolve against the current working directory — the package root under `lake build`; current cwd: '{toString (← IO.currentDir)}')"
  let envl ←
    match parseEnvelopeString contents with
    | .error e =>
        throwErrorAt path "load_es_program: '{pathStr}' is not a valid es-0.2 envelope: {e}"
    | .ok envl => pure envl
  unless envl.schemaVersion == acceptedSchema do
    throwErrorAt path
      "load_es_program: '{pathStr}' has schema_version '{envl.schemaVersion}', expected '{acceptedSchema}'"
  unless envl.languageVersion == acceptedEdition do
    throwErrorAt path
      "load_es_program: '{pathStr}' was extracted for edition '{envl.languageVersion}', but this ingester pins '{acceptedEdition}'. The edition is an INPUT to the AST, not a stamp on it — the grammar a parser accepts is a function of it, so an envelope from another edition is a different program (docs/es-envelope-schema.md §0)."
  let declName := (← getCurrNamespace) ++ name.getId
  if (← getEnv).contains declName then
    throwErrorAt name "load_es_program: '{declName}' has already been declared"
  liftCoreM do
    addAndCompile <| .defnDecl {
      name := declName
      levelParams := []
      type := Lean.mkConst ``LeanModels.Es.Envelope
      value := Lean.toExpr envl
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst declName
    addDocStringCore declName
      s!"ECMAScript envelope loaded by `load_es_program` from `{pathStr}` (source: `{envl.sourceFile}`, sha256 `{envl.sourceSha256}`, edition `{envl.languageVersion}`)."
  liftTermElabM do
    Term.addTermInfo' name (Lean.mkConst declName) (isBinder := true)

end LeanModels.Es
