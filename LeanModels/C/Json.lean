import Lean
import LeanModels.C.Ast

/-!
# `c-0.1` envelope ingestion (`LeanModels.C`)

Parses the envelope of `docs/c-envelope-schema.md` from `Lean.Json` into
the types of `Ast.lean`. All parsers are pure and return
`Except String _`; malformed or unknown input yields a descriptive
`.error`, never a panic.

Entry points: `parseEnvelope : Lean.Json → Except String Envelope` and
`parseEnvelopeString : String → Except String Envelope`.

**This lane defines its own helpers rather than importing the Python
lane's.** `LeanModels/C/` is a SIBLING of `LeanModels/Python/`, never a
client of it (`docs/c-tier-charter.md` §2.1) — the two share the
project's covenant and its instruments, not its values. The helpers below
are twenty lines; coupling the two tiers to save them would be trading a
structural decision for a rounding error.

Notes:
* Field names match the schema exactly (`schema_version`, `profile_id`,
  `translation_unit`, `c_kind`, `end_line`, …).
* the full `frontend.version` is retained and checked against the pinned
  compiler identity. `profile_id` is retained because the profile is an INPUT
  to the AST, so a mismatch has to be refusable downstream.
* An unknown `kind` is NOT an error — the extractor has already turned it
  into an `Unsupported` leaf, and this reproduces that faithfully. An
  unknown kind arriving here anyway means the extractor and the ingester
  disagree about the vocabulary, which IS an error and says so.
-/

namespace LeanModels.C

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

/-- A field that may be JSON `null` or absent. -/
def getOptStr (j : Json) (name : String) : Except String (Option String) :=
  match j.getObjVal? name with
  | .error _ => .ok none
  | .ok .null => .ok none
  | .ok v => withCtx s!"field '{name}'" (some <$> v.getStr?)

def getOptNat (j : Json) (name : String) : Except String (Option Nat) :=
  match j.getObjVal? name with
  | .error _ => .ok none
  | .ok .null => .ok none
  | .ok v => withCtx s!"field '{name}'" (some <$> v.getNat?)

def getOptNatList (j : Json) (name : String) : Except String (Option (List Nat)) :=
  match j.getObjVal? name with
  | .error _ | .ok .null => .ok none
  | .ok (.arr values) => do
      let result ← values.toList.mapM (fun v => withCtx s!"field '{name}'" v.getNat?)
      pure (some result)
  | .ok _ => .error s!"field '{name}' is not an array"

/-- A required array field, as a list. -/
def getArr (j : Json) (name : String) : Except String (List Json) := do
  match ← getField j name with
  | .arr a => return a.toList
  | _ => throw s!"field '{name}' is not an array"

/-- A field that is either a node or JSON `null`/absent. -/
def getOptNode (j : Json) (name : String) : Option Json :=
  match j.getObjVal? name with
  | .error _ => none
  | .ok .null => none
  | .ok v => some v

def getOptFieldName (j : Json) : Except String (Option String) :=
  match j.getObjVal? "field" with
  | .error _ | .ok .null => .ok none
  | .ok v =>
      match v with
      | .str s => .ok (some s)
      | _ =>
          match v.getObjValAs? String "name" with
          | .ok s => .ok (some s)
          | .error e => .error e

def getFrontendVersion (j : Json) : Except String String := do
  let frontend ← getField j "frontend"
  withCtx "field 'frontend'" (getStr frontend "version")

def getBool (j : Json) (name : String) : Except String Bool :=
  match j.getObjVal? name with
  | .error _ => .ok false
  | .ok .null => .ok false
  | .ok v => withCtx s!"field '{name}'" v.getBool?

/-! ## Spans and types -/

def parseSpan (j : Json) : Except String CSpan :=
  withCtx "span" do
    -- `col`/`end_col` are OPTIONAL: absent and `null` are the same absence,
    -- which is the reading `getOptNat` already gives the macro fields.
    return { line := ← getNat j "line", col := ← getOptNat j "col"
             endLine := ← getNat j "end_line", endCol := ← getOptNat j "end_col"
             macroLine := ← (match getOptNode j "macro" with
                             | none => pure none
                             | some m => getOptNat m "line")
             macroCol := ← (match getOptNode j "macro" with
                            | none => pure none
                            | some m => getOptNat m "col") }

/-- The span of a node, read from its `"span"` field. -/
def nodeSpan (j : Json) : Except String CSpan := do
  parseSpan (← getField j "span")

partial def parseTypeNode (j : Json) : Except String TypeNode := do
  let kind ← getStr j "kind"
  withCtx kind do
    let inner : Except String TypeNode := match getOptNode j "inner" with
      | none => .ok (.unsupported kind "missing inner")
      | some v => parseTypeNode v
    match kind with
    | "BuiltinType" => return .builtin (← getStr j "name")
    | "PointerType" => return .pointer (← inner)
    | "ParenType" => return .paren (← inner)
    | "ElaboratedType" => return .elaborated (← inner)
    | "RecordType" => return .record (← getStr j "type")
    | "TypedefType" => return .typedefRef (← getStr j "type")
    | "FunctionProtoType" =>
        let ret ← match getOptNode j "ret" with
          | none => throw "missing 'ret'"
          | some v => parseTypeNode v
        let ps ← (← getArr j "params").mapM parseTypeNode
        return .funcProto ret ps
    | "Unsupported" =>
        return .unsupported (← getStr j "c_kind") (← getStr j "text")
    | other => throw s!"unknown type kind {other.quote}"

/-! ## Expressions -/

partial def parseExpr (j : Json) : Except String Expr := do
  let kind ← getStr j "kind"
  withCtx kind do
    let span ← nodeSpan j
    let ty : Except String CType := getStr j "type"
    let sub (n : String) : Except String Expr := match getOptNode j n with
      | none => .error s!"missing '{n}'"
      | some v => parseExpr v
    let optSub (n : String) : Except String (Option Expr) :=
      match getOptNode j n with
      | none => .ok none
      | some v => some <$> parseExpr v
    match kind with
    | "IntegerLiteral" => return .intLit (← getStr j "value") (← ty) span
    | "CharacterLiteral" =>
        -- clang gives the code point as a NUMBER; keep the decimal spelling.
        let v ← getField j "value"
        return .charLit (match v with
                         | .num n => toString n
                         | _ => v.compress) (← ty) span
    | "StringLiteral" =>
        let value ← getStr j "value"
        let decoded ← getOptNatList j "decoded_bytes"
        let typ ← ty
        return .strLit value decoded typ span
    | "FloatingLiteral" =>
        let v ← getField j "value"
        let bitsHex ← getOptStr j "float_bits_hex"
        let bitWidth ← getOptNat j "float_bit_width"
        return .floatLit (match v with
                          | .str s => s
                          | .num n => toString n
                          | _ => v.compress) bitsHex bitWidth (← ty) span
    | "CXXBoolLiteralExpr" =>
        return .boolLit (← getBool j "value") (← ty) span
    | "ChooseExpr" =>
        return .choose (← sub "cond") (← sub "then") (← sub "else") (← ty) span
    | "DeclRefExpr" =>
        let id ← getOptStr j "decl_id"
        return .declRef (id.map DeclarationId.mk) (← getStr j "name")
          (← getStr j "decl_kind") (← ty) span
    | "MemberExpr" =>
        return .member (← sub "base") (← getStr j "member")
          (← getBool j "arrow") (← ty) span
    | "ArraySubscriptExpr" =>
        return .index (← sub "base") (← sub "index") (← ty) span
    | "CallExpr" =>
        return .call (← sub "callee")
          (← (← getArr j "args").mapM parseExpr) (← ty) span
    | "BinaryOperator" =>
        return .binop (← getStr j "op") (← sub "lhs") (← sub "rhs") (← ty) span
    | "CompoundAssignOperator" =>
        return .compoundAssign (← getStr j "op") (← sub "lhs") (← sub "rhs")
          (← getStr j "compute_lhs_type") (← getStr j "compute_result_type")
          (← ty) span
    | "UnaryOperator" =>
        return .unop (← getStr j "op") (← sub "sub") (← getBool j "postfix")
          (← ty) span
    | "ConditionalOperator" =>
        return .cond (← sub "cond") (← sub "then") (← sub "else") (← ty) span
    | "ParenExpr" => return .paren (← sub "sub") (← ty) span
    | "ImplicitCastExpr" =>
        return .implicitCast (← getStr j "cast") (← sub "sub") (← ty) span
    | "CStyleCastExpr" =>
        return .cast (← getStr j "cast") (← sub "sub") (← ty) span
    | "InitListExpr" =>
        let inits ← (← getArr j "inits").mapM parseExpr
        let field ← getOptFieldName j
        -- This field is mandatory: legacy c-0.1 envelopes silently dropped
        -- positional fillers, so accepting an absent field can change a program.
        match ← getField j "array_filler" with
        | .null => return .initList inits field (← ty) span
        | .arr filler => return .arrayInitList inits (← filler.toList.mapM parseExpr) field (← ty) span
        | _ => throw "field 'array_filler' is not an array or null"
    | "ImplicitValueInitExpr" => return .implicitValueInit (← ty) span
    | "CompoundLiteralExpr" => return .compoundLit (← sub "init") (← ty) span
    | "UnaryExprOrTypeTraitExpr" =>
        return .typeTrait (← getStr j "trait") (← getOptStr j "arg_type")
          (← optSub "sub") (← ty) span
    | "ConstantExpr" =>
        let value? ← getOptStr j "value"
        match value? with
        | some value => return .constExpr value (← optSub "sub") (← ty) span
        | none => return .unsupported "ConstantExpr" "unfolded constant expression" span
    | "Unsupported" =>
        return .unsupported (← getStr j "c_kind") (← getStr j "text") span
    | other =>
        -- The extractor is supposed to have refused this already.  If one
        -- arrives, the two halves disagree about the vocabulary, and that
        -- is a defect rather than an unsupported program.
        throw s!"unknown expression kind {other.quote} (the extractor should \
have emitted an Unsupported leaf; extractor and ingester disagree)"

/-! ## Declarations and statements -/

partial def parseDecl (j : Json) : Except String Decl := do
  let kind ← getStr j "kind"
  withCtx kind do
    let span ← nodeSpan j
    match kind with
    | "VarDecl" =>
        let id ← getOptStr j "decl_id"
        return .var (id.map DeclarationId.mk) (← getStr j "name") (← getStr j "type")
          (← getOptStr j "storage")
          (← match getOptNode j "init" with
              | none => pure none
              | some v => some <$> parseExpr v)
          ((← getOptStr j "record_decl_id").map DeclarationId.mk) span
    -- `name` is OPTIONAL (§6.7.6.3): absent and `null` are one absence.
    | "ParmVarDecl" =>
        let id ← getOptStr j "decl_id"
        return .param (id.map DeclarationId.mk) (← getOptStr j "name")
          (← getStr j "type") span
    | "FieldDecl" =>
        return .field (← getOptStr j "name") (← getStr j "type") (← getOptNat j "bits") span
    | "RecordDecl" =>
        return .record ((← getOptStr j "decl_id").map DeclarationId.mk) (← getOptStr j "name")
          (← (← getArr j "fields").mapM parseDecl) span
    | "TypedefDecl" =>
        return .typedef (← getStr j "name") (← getStr j "type")
          (← match getOptNode j "underlying" with
              | none => pure none
              | some v => some <$> parseTypeNode v) span
    | "EnumDecl" =>
        return .enum (← getOptStr j "name")
          (← (← getArr j "constants").mapM parseDecl) span
    | "EnumConstantDecl" =>
        -- `value` is OPTIONAL: clang does not always fold one.
        let id ← getOptStr j "decl_id"
        return .enumConst (id.map DeclarationId.mk) (← getStr j "name")
          (← getOptStr j "value") span
    | "EmptyDecl" => return .empty span
    | "Unsupported" =>
        return .unsupported (← getStr j "c_kind") (← getStr j "text") span
    | other => return .unsupported other "unmodeled declaration" span

partial def parseStmt (j : Json) : Except String Stmt := do
  let kind ← getStr j "kind"
  withCtx kind do
    let span ← nodeSpan j
    let stmt (n : String) : Except String Stmt := match getOptNode j n with
      | none => .error s!"missing '{n}'"
      | some v => parseStmt v
    let optStmt (n : String) : Except String (Option Stmt) :=
      match getOptNode j n with
      | none => .ok none
      | some v => some <$> parseStmt v
    let expr (n : String) : Except String Expr := match getOptNode j n with
      | none => .error s!"missing '{n}'"
      | some v => parseExpr v
    let optExpr (n : String) : Except String (Option Expr) :=
      match getOptNode j n with
      | none => .ok none
      | some v => some <$> parseExpr v
    match kind with
    | "CompoundStmt" =>
        return .compound (← (← getArr j "body").mapM parseStmt) span
    | "DeclStmt" => return .decl (← (← getArr j "decls").mapM parseDecl) span
    | "IfStmt" =>
        return .ifS (← expr "cond") (← stmt "then") (← optStmt "else") span
    | "ForStmt" =>
        return .forS (← optStmt "init") (← optExpr "cond") (← optExpr "inc")
          (← stmt "body") span
    | "WhileStmt" => return .whileS (← expr "cond") (← stmt "body") span
    | "DoStmt" => return .doS (← stmt "body") (← expr "cond") span
    | "ReturnStmt" => return .ret (← optExpr "value") span
    | "BreakStmt" => return .breakS span
    | "ContinueStmt" => return .continueS span
    | "NullStmt" => return .nullStmt span
    | "SwitchStmt" => return .switchS (← expr "cond") (← stmt "body") span
    | "CaseStmt" =>
        if (← getBool j "gnu_range") then
          return .caseRange (← expr "lo") (← expr "hi") (← stmt "body") span
        else
          match expr "value" with
          | .ok value => return .caseS value (← stmt "body") span
          | .error reason => return .unsupported "CaseStmt" reason span
    | "DefaultStmt" => return .defaultS (← stmt "body") span
    | "GotoStmt" => return .goto (← getStr j "label") span
    | "LabelStmt" => return .label (← getStr j "label") (← stmt "body") span
    | "Unsupported" =>
        return .unsupported (← getStr j "c_kind") (← getStr j "text") span
    | _ =>
        -- Anything else in statement position is an EXPRESSION statement:
        -- clang puts the expression there directly, with no wrapper node.
        return .expr (← parseExpr j) span

/-! ## The envelope -/

def parseFunctionDefn (j : Json) : Except String FunctionDefn :=
  withCtx "FunctionDecl" do
    let id ← getOptStr j "decl_id"
    return { id := id.map DeclarationId.mk, name := ← getStr j "name", ty := ← getStr j "type"
             storage := ← getOptStr j "storage"
             params := ← (← getArr j "params").mapM parseDecl
             body := ← (match getOptNode j "body" with
                        | none => pure none
                        | some v => some <$> parseStmt v)
             span := ← nodeSpan j }

def parseTopLevel (j : Json) : Except String TopLevel := do
  match ← getStr j "kind" with
  | "FunctionDecl" => return .fn (← parseFunctionDefn j)
  | _ => return .decl (← parseDecl j)

def parseExternal (j : Json) : Except String External :=
  withCtx "external" do
    return { name := ← getStr j "name", ty := ← getOptStr j "type" }

def parseEnvelope (j : Json) : Except String Envelope := withCtx "envelope" do
  let ver ← getStr j "schema_version"
  unless ver == "c-0.1" do
    throw s!"unsupported schema_version {ver.quote} (this ingester reads 'c-0.1')"
  let tu ← getField j "translation_unit"
  let frontendVersion ← getFrontendVersion j
  unless frontendVersion == pinnedFrontendVersion do
    throw s!"unsupported frontend.version {frontendVersion.quote} (this ingester pins {pinnedFrontendVersion.quote})"
  return { schemaVersion := ver
           language := ← getStr j "language"
           frontendVersion
           profileId := ← getStr j "profile_id"
           profileFlags := ← (← getArr j "profile_flags").mapM (·.getStr?)
           sourceFile := ← getStr j "source_file"
           sourceSha256 := ← getStr j "source_sha256"
           unit := { items := ← (← getArr tu "decls").mapM parseTopLevel }
           externals := ← (← getArr j "externals").mapM parseExternal }

def parseEnvelopeString (s : String) : Except String Envelope := do
  match Json.parse s with
  | .error e => .error s!"invalid JSON: {e}"
  | .ok j => parseEnvelope j

end LeanModels.C
