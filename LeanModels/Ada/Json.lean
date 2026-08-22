import Lean
import LeanModels.Ada.Ast

/-!
# `ada-0.1` envelope ingestion (`LeanModels.Ada`)

Parses the envelope of `docs/ada-envelope-schema.md` from `Lean.Json` into
the types of `Ast.lean`. All parsers are pure and return
`Except String _`; malformed or unknown input yields a descriptive
`.error`, never a panic.

Entry points: `parseEnvelope : Lean.Json → Except String Envelope` and
`parseEnvelopeString : String → Except String Envelope`.

**This lane defines its own helpers rather than importing the C lane's.**
`LeanModels/Ada/` is a SIBLING of `LeanModels/C/` and `LeanModels/Python/`,
never a client (`docs/c-tier-charter.md` §2.1, inherited by
`docs/ada-charter.md` §5.6). The helpers are twenty lines; coupling three
tiers to save them would trade a structural decision for a rounding error.

## The vocabulary is a PARAMETER, and that is the whole design

`parseNode` takes the accepted kind set. It is not baked in, because
`docs/ada-envelope-schema.md` §3 makes `docs/ada-construct-census.json`'s
`node_kinds` the single source of truth and a second copy in Lean would be
the drift that document refuses. `load_ada_program` supplies it from the
census file at elaboration time.

An unknown `kind` arriving here is an ERROR, not an `unsupported` leaf — the
extractor has already turned out-of-vocabulary nodes into `Unsupported`
leaves, so a stray kind means the extractor and the ingester disagree about
the vocabulary, which is exactly the drift the gate exists to catch.
-/

namespace LeanModels.Ada

open Lean (Json)

/-! ## Helpers -/

/-- Prefix an error with the context it happened in. -/
def withCtx (ctx : String) (r : Except String α) : Except String α :=
  match r with
  | .ok a => .ok a
  | .error e => .error s!"{ctx}: {e}"

/-- A required field. -/
def getField (j : Json) (name : String) : Except String Json :=
  match j.getObjVal? name with
  | .ok v => .ok v
  | .error _ => .error s!"missing field '{name}'"

/-- A required string field. -/
def getStr (j : Json) (name : String) : Except String String := do
  let v ← getField j name
  withCtx s!"field '{name}'" v.getStr?

/-- A required natural-number field. -/
def getNat (j : Json) (name : String) : Except String Nat := do
  let v ← getField j name
  withCtx s!"field '{name}'" v.getNat?

/-- An optional string field: absent or JSON `null` both give `none`. -/
def getStr? (j : Json) (name : String) : Except String (Option String) :=
  match j.getObjVal? name with
  | .error _ => .ok none
  | .ok .null => .ok none
  | .ok v => do let s ← withCtx s!"field '{name}'" v.getStr?; pure (some s)

/-- A required array field. -/
def getArr (j : Json) (name : String) : Except String (Array Json) := do
  let v ← getField j name
  match v with
  | .arr a => .ok a
  | _ => .error s!"field '{name}': expected an array"

/-- Map a parser over an array, reporting the index that failed. -/
def mapIdx (a : Array Json) (f : Json → Except String α) :
    Except String (Array α) :=
  a.foldlM (init := #[]) fun acc j => do
    let v ← withCtx s!"element {acc.size}" (f j)
    pure (acc.push v)

/-! ## Nodes -/

/-- A span. All four components are required (`Ast.lean`'s `AdaSpan`). -/
def parseSpan (j : Json) : Except String AdaSpan := do
  let s ← getField j "span"
  pure {
    line := ← getNat s "line", col := ← getNat s "col",
    endLine := ← getNat s "end_line", endCol := ← getNat s "end_col" }

/--
One node.

`vocab` is the accepted kind set — see the module docstring. A JSON `null`
child becomes `Node.absent`, because in Ada an absent optional field is
meaningful.
-/
partial def parseNode (vocab : Std.HashSet String) : Json → Except String Node
  | .null => .ok .absent
  | j => do
    let kind ← getStr j "kind"
    let span ← parseSpan j
    if kind == "Unsupported" then
      pure (.unsupported (← getStr j "node_class") span (← getStr j "text"))
    else if !vocab.contains kind then
      .error s!"node kind '{kind}' is not in the census vocabulary — the \
extractor should have emitted an Unsupported leaf, so this means the \
extractor and the ingester disagree about the vocabulary \
(docs/ada-envelope-schema.md §3)"
    else
      match j.getObjVal? "children" with
      | .ok (.arr cs) => pure (.node kind span (← mapIdx cs (parseNode vocab)))
      | _ => pure (.leaf kind span (← getStr j "text"))

/-! ## The envelope's parts -/

def parseSourceFile (j : Json) : Except String SourceFile := do
  pure { path := ← getStr j "path", sha256 := ← getStr j "sha256",
         lineEndings := ← getStr j "line_endings" }

def parseMarking (j : Json) : Except String Marking := do
  pure {
    kind := ← getStr j "kind", file := ← getNat j "file",
    line := ← getNat j "line", col := ← getNat j "col",
    endLine := ← getNat j "end_line", endCol := ← getNat j "end_col",
    text := ← getStr j "text" }

def parseDiagnostic (j : Json) : Except String Diagnostic := do
  pure { file := ← getNat j "file", message := ← getStr j "message" }

def parseUnit (vocab : Std.HashSet String) (j : Json) :
    Except String CompilationUnit := do
  pure {
    name := ← getStr? j "name", kind := ← getStr? j "kind",
    file := ← getNat j "file", order := ← getNat j "order",
    position := ← getNat j "position", span := ← parseSpan j,
    decl := ← withCtx "decl" (parseNode vocab (← getField j "decl")) }

/-- The whole envelope. `frontend` is accepted and NOT retained — it is a
stamp. `profileId` and `languageVersion` ARE retained: both are INPUTS to
the program, so a mismatch has to be refusable downstream. -/
def parseEnvelope (vocab : Std.HashSet String) (j : Json) :
    Except String Envelope := do
  pure {
    schemaVersion := ← getStr j "schema_version",
    language := ← getStr j "language",
    languageVersion := ← getStr j "language_version",
    profileId := ← getStr j "profile_id",
    sourceFiles := ← withCtx "source_files"
      (mapIdx (← getArr j "source_files") parseSourceFile),
    compilationUnits := ← withCtx "compilation_units"
      (mapIdx (← getArr j "compilation_units") (parseUnit vocab)),
    markings := ← withCtx "markings" (mapIdx (← getArr j "markings") parseMarking),
    diagnostics := ← withCtx "diagnostics"
      (mapIdx (← getArr j "diagnostics") parseDiagnostic),
    unsupportedCount := ← getNat j "unsupported_count" }

def parseEnvelopeString (vocab : Std.HashSet String) (s : String) :
    Except String Envelope := do
  parseEnvelope vocab (← Json.parse s)

/-- The census file's `node_kinds`, which `docs/ada-envelope-schema.md` §3
makes the single source of truth for the accepted vocabulary. -/
def parseVocabString (s : String) : Except String (Std.HashSet String) := do
  let j ← Json.parse s
  let ks ← getArr j "node_kinds"
  let names ← mapIdx ks (fun k => k.getStr?)
  if names.isEmpty then
    .error "the census carries no node_kinds — an empty vocabulary would \
make every node an error, which is an instrument fault and not a finding"
  else
    .ok (names.foldl (fun (acc : Std.HashSet String) n => acc.insert n) ∅)

end LeanModels.Ada
