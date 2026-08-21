import LeanModels.C.Json

/-!
# `load_c_program` — elaboration-time envelope ingestion (`LeanModels.C`)

The C lane's analogue of the Python lane's `load_program`: read a `c-0.1`
envelope at ELABORATION time and define its translation unit as a
**literal** first-order term, so `#guard`s (and later, proofs) can unfold
it.

    load_c_program sunfishC from "Examples/c/sunfish/sunfish.json"

Missing files, malformed envelopes, a wrong `language`, and a wrong
`schema_version` are all clear elaboration errors, never silent. The
`profile_id` is REFUSED when it does not match the ingester's pin —
unlike a frontend stamp, the profile is an INPUT to the AST
(`docs/c-envelope-schema.md` §0), so an envelope extracted under another
profile is a different program and must not be quietly accepted.
-/

namespace LeanModels.C

deriving instance Lean.ToExpr for CSpan
deriving instance Lean.ToExpr for TypeNode
deriving instance Lean.ToExpr for Expr
deriving instance Lean.ToExpr for Decl
deriving instance Lean.ToExpr for Stmt
deriving instance Lean.ToExpr for FunctionDefn
deriving instance Lean.ToExpr for TopLevel
deriving instance Lean.ToExpr for TranslationUnit
deriving instance Lean.ToExpr for External
deriving instance Lean.ToExpr for Envelope

/-- The profile this ingester accepts. See the module docstring: a
mismatch is refused rather than stamped. -/
def acceptedProfile : String := "c-profile-0.1"

open Lean Elab Command in
/--
`load_c_program e from "path.json"` reads the `c-0.1` envelope at
elaboration time and defines `e : Envelope` as a literal term — the whole
envelope, not just its translation unit, because `externals` (the 27-name
libc slice) is a claim the ingester must be checkable against too.
The path resolves against the current working directory — the package
root under `lake build`.
-/
elab "load_c_program " name:ident " from " path:str : command => do
  let pathStr := path.getString
  let contents ←
    match ← (IO.FS.readFile ⟨pathStr⟩).toBaseIO with
    | .ok c => pure c
    | .error e =>
        throwErrorAt path
          "load_c_program: cannot read '{pathStr}': {toString e}\n(relative paths resolve against the current working directory — the package root under `lake build`; current cwd: '{toString (← IO.currentDir)}')"
  let envl ←
    match parseEnvelopeString contents with
    | .error e =>
        throwErrorAt path "load_c_program: '{pathStr}' is not a valid c-0.1 envelope: {e}"
    | .ok envl => pure envl
  unless envl.language == "c" do
    throwErrorAt path
      "load_c_program: '{pathStr}' has language '{envl.language}', expected 'c'"
  unless envl.profileId == acceptedProfile do
    throwErrorAt path
      "load_c_program: '{pathStr}' was extracted under profile '{envl.profileId}', but this ingester pins '{acceptedProfile}'. The profile is an INPUT to the AST, not a stamp on it — an envelope from another profile is a different program (docs/c-envelope-schema.md §0)."
  let declName := (← getCurrNamespace) ++ name.getId
  if (← getEnv).contains declName then
    throwErrorAt name "load_c_program: '{declName}' has already been declared"
  liftCoreM do
    addAndCompile <| .defnDecl {
      name := declName
      levelParams := []
      type := Lean.mkConst ``LeanModels.C.Envelope
      value := Lean.toExpr envl
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst declName
    addDocStringCore declName
      s!"C translation unit loaded by `load_c_program` from `{pathStr}` (source: `{envl.sourceFile}`, sha256 `{envl.sourceSha256}`, profile `{envl.profileId}`). A literal `LeanModels.C.Envelope`; its translation unit is `.unit`."
  liftTermElabM do
    Term.addTermInfo' name (Lean.mkConst declName) (isBinder := true)

end LeanModels.C
