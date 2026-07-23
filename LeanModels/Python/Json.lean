import Lean
import LeanModels.Python.Ast

/-!
# Envelope JSON ingestion (`LeanModels.Python`)

Parses the standardized AST envelope of `docs/envelope-schema.md` (schema v0.1,
Python payload) from `Lean.Json` into the types of `Ast.lean`. All parsers are
pure and return `Except String _`; malformed or unknown input yields a
descriptive `.error`, never a panic. IO helpers belong to later phases.

Entry points: `parseEnvelope : Lean.Json → Except String Envelope` and the
convenience `parseEnvelopeString : String → Except String Envelope`.

Notes:
* Field names match the schema doc exactly (`schema_version`, `source_file`,
  `args_unsupported`, `py_kind`, `first_line`, …).
* The envelope's `frontend` field is accepted but not retained.
* Int constants arrive as decimal strings (`{"type":"int","repr":"123"}`).
* A `FunctionDef` at module top level becomes a `FunctionDefn`; a *nested*
  `def` is ingested as `Stmt.unsupported "FunctionDef" name span`.
-/

namespace LeanModels.Python

open Lean (Json)

/-- One `# lean[ … # ]` block: `{"first_line": …, "last_line": …, "text": …}`.
`firstLine`/`lastLine` are the 1-based source lines of the `# lean[` / `# ]`
markers; `text` is the joined inner lines, no trailing newline. -/
structure LeanBlock where
  firstLine : Nat
  lastLine : Nat
  text : String
deriving Repr, Inhabited, BEq, DecidableEq

/-- The full envelope (one per source file). `frontend` is not retained. -/
structure Envelope where
  schemaVersion : String
  language : String
  sourceFile : String
  sourceSha256 : String
  module : Module
  leanBlocks : Array LeanBlock
deriving Repr, Inhabited, BEq

/-- Prefix an error message with context. -/
private def withCtx (c : String) : Except String α → Except String α
  | .ok a => .ok a
  | .error e => .error s!"{c}: {e}"

/-- Required object field. -/
private def getField (j : Json) (name : String) : Except String Json :=
  withCtx s!"field '{name}'" (j.getObjVal? name)

/-- Nullable string field: absent or `null` ↦ `none`, string ↦ `some`. -/
private def getOptStrField (j : Json) (name : String) : Except String (Option String) :=
  match j.getObjVal? name with
  | .error _ => pure Option.none
  | .ok .null => pure Option.none
  | .ok v => withCtx s!"field '{name}'" do pure (some (← v.getStr?))

def parseSpan (j : Json) : Except String Span :=
  withCtx "span" do
    return { lineno := ← (← getField j "lineno").getNat?
             colOffset := ← (← getField j "col_offset").getNat?
             endLineno := ← (← getField j "end_lineno").getNat?
             endColOffset := ← (← getField j "end_col_offset").getNat? }

def parseBinOpName : String → Except String BinOp
  | "Add" => .ok .add
  | "Sub" => .ok .sub
  | "Mult" => .ok .mult
  | "FloorDiv" => .ok .floorDiv
  | "Mod" => .ok .mod
  | "Pow" => .ok .pow
  | s => .error s!"unknown BinOp name {s.quote}"

def parseUnaryOpName : String → Except String UnaryOp
  | "USub" => .ok .usub
  | "Not" => .ok .not
  | s => .error s!"unknown UnaryOp name {s.quote}"

def parseBoolOpName : String → Except String BoolOp
  | "And" => .ok .and
  | "Or" => .ok .or
  | s => .error s!"unknown BoolOp name {s.quote}"

def parseCmpOpName : String → Except String CmpOp
  | "Eq" => .ok .eq
  | "NotEq" => .ok .notEq
  | "Lt" => .ok .lt
  | "LtE" => .ok .ltE
  | "Gt" => .ok .gt
  | "GtE" => .ok .gtE
  | s => .error s!"unknown CmpOp name {s.quote}"

/-- Parse a schema constant payload (the `value` of a `Constant` node). -/
def parseConst (j : Json) : Except String Const :=
  withCtx "Constant" do
    let ty ← (← getField j "type").getStr?
    match ty with
    | "int" =>
        let r ← (← getField j "repr").getStr?
        match r.toInt? with
        | some n => pure (Const.int n)
        | Option.none => throw s!"invalid int repr {r.quote}"
    | "bool" => return Const.bool (← (← getField j "value").getBool?)
    | "str" => return Const.str (← (← getField j "value").getStr?)
    | "none" => pure Const.none
    | other => throw s!"unknown const type {other.quote}"

/-- Parse an expression node. `partial` because the recursion is over the
`Json` tree (through object/array lookups), not structural; parsing is
executable code only — nothing downstream proves theorems about it. -/
partial def parseExpr (j : Json) : Except String Expr := do
  let kind ← (← getField j "kind").getStr?
  withCtx kind do
    let span ← parseSpan (← getField j "span")
    match kind with
    | "Constant" =>
        return .constant (← parseConst (← getField j "value")) span
    | "Name" =>
        return .name (← (← getField j "id").getStr?) span
    | "BinOp" =>
        let left ← parseExpr (← getField j "left")
        let op ← parseBinOpName (← (← getField j "op").getStr?)
        let right ← parseExpr (← getField j "right")
        return .binOp left op right span
    | "UnaryOp" =>
        let op ← parseUnaryOpName (← (← getField j "op").getStr?)
        return .unaryOp op (← parseExpr (← getField j "operand")) span
    | "BoolOp" =>
        let op ← parseBoolOpName (← (← getField j "op").getStr?)
        let values ← (← (← getField j "values").getArr?).mapM parseExpr
        return .boolOp op values span
    | "Compare" =>
        let left ← parseExpr (← getField j "left")
        let ops ← (← (← getField j "ops").getArr?).mapM fun o => do
          parseCmpOpName (← o.getStr?)
        let comparators ← (← getField j "comparators").getArr? >>= (·.mapM parseExpr)
        if ops.size != comparators.size then
          throw s!"ops/comparators length mismatch ({ops.size} vs {comparators.size})"
        return .compare left ops comparators span
    | "Call" =>
        let func ← parseExpr (← getField j "func")
        let args ← (← (← getField j "args").getArr?).mapM parseExpr
        let cu ← getOptStrField j "call_unsupported"
        return .call func args cu span
    | "List" =>
        return .list (← (← (← getField j "elts").getArr?).mapM parseExpr) span
    | "Tuple" =>
        return .tuple (← (← (← getField j "elts").getArr?).mapM parseExpr) span
    | "Subscript" =>
        let value ← parseExpr (← getField j "value")
        let index ← parseExpr (← getField j "index")
        return .subscript value index span
    | "Unsupported" =>
        return .unsupported (← (← getField j "py_kind").getStr?)
          (← (← getField j "text").getStr?) span
    | other => throw s!"unknown expression kind {other.quote}"

/-- Parse a statement node (see `parseExpr` for why `partial`). -/
partial def parseStmt (j : Json) : Except String Stmt := do
  let kind ← (← getField j "kind").getStr?
  withCtx kind do
    let span ← parseSpan (← getField j "span")
    match kind with
    | "Return" =>
        let value ← match ← getField j "value" with
          | .null => pure Option.none
          | jv => do pure (some (← parseExpr jv))
        return .ret value span
    | "Assign" =>
        let targets ← (← (← getField j "targets").getArr?).mapM parseExpr
        return .assign targets (← parseExpr (← getField j "value")) span
    | "AugAssign" =>
        let target ← parseExpr (← getField j "target")
        let op ← parseBinOpName (← (← getField j "op").getStr?)
        return .augAssign target op (← parseExpr (← getField j "value")) span
    | "While" =>
        return .whileLoop (← parseExpr (← getField j "test"))
          (← (← (← getField j "body").getArr?).mapM parseStmt)
          (← (← (← getField j "orelse").getArr?).mapM parseStmt) span
    | "If" =>
        return .ifStmt (← parseExpr (← getField j "test"))
          (← (← (← getField j "body").getArr?).mapM parseStmt)
          (← (← (← getField j "orelse").getArr?).mapM parseStmt) span
    | "Expr" =>
        return .exprStmt (← parseExpr (← getField j "value")) span
    | "Pass" => return .pass span
    | "Break" => return .brk span
    | "Continue" => return .cont span
    | "Unsupported" =>
        return .unsupported (← (← getField j "py_kind").getStr?)
          (← (← getField j "text").getStr?) span
    | "FunctionDef" =>
        -- Nested `def` (module-level ones are split out by `parseModule`).
        -- Representation coverage: keep ingestion total, mark it unsupported.
        let name := ((← getField j "name").getStr?).toOption.getD ""
        return .unsupported "FunctionDef" name span
    | other => throw s!"unknown statement kind {other.quote}"

def parseParam (j : Json) : Except String Param :=
  withCtx "param" do
    return { arg := ← (← getField j "arg").getStr?
             span := ← parseSpan (← getField j "span") }

/-- Parse a module-level `FunctionDef` node into a `FunctionDefn`.
`argsOk` is `true` iff `args_unsupported` is `null` (or absent); `localsOk`
likewise from `locals_unsupported` (absent in older envelopes ⇒ `true`). -/
def parseFunctionDefn (j : Json) : Except String FunctionDefn :=
  withCtx "FunctionDef" do
    let name ← (← getField j "name").getStr?
    let span ← parseSpan (← getField j "span")
    let params ← (← (← getField j "args").getArr?).mapM parseParam
    let argsUnsupported ← getOptStrField j "args_unsupported"
    let localsUnsupported ← getOptStrField j "locals_unsupported"
    let body ← (← (← getField j "body").getArr?).mapM parseStmt
    return { name, params, argsOk := argsUnsupported.isNone,
             localsOk := localsUnsupported.isNone, body, span }

/-- Parse the `module` payload, splitting top-level `FunctionDef`s into
`Module.functions` and everything else into `Module.topLevel` (source order
preserved within each). -/
def parseModule (j : Json) : Except String Module :=
  withCtx "module" do
    let kind ← (← getField j "kind").getStr?
    unless kind == "Module" do
      throw s!"expected kind \"Module\", got {kind.quote}"
    let body ← (← getField j "body").getArr?
    let mut functions : Array FunctionDefn := #[]
    let mut topLevel : Array Stmt := #[]
    for stmtJson in body do
      let k ← (← getField stmtJson "kind").getStr?
      if k == "FunctionDef" then
        functions := functions.push (← parseFunctionDefn stmtJson)
      else
        topLevel := topLevel.push (← parseStmt stmtJson)
    return { functions, topLevel }

def parseLeanBlock (j : Json) : Except String LeanBlock :=
  withCtx "lean_blocks" do
    return { firstLine := ← (← getField j "first_line").getNat?
             lastLine := ← (← getField j "last_line").getNat?
             text := ← (← getField j "text").getStr? }

/-- Parse a full envelope document. -/
def parseEnvelope (j : Json) : Except String Envelope :=
  withCtx "envelope" do
    return { schemaVersion := ← (← getField j "schema_version").getStr?
             language := ← (← getField j "language").getStr?
             sourceFile := ← (← getField j "source_file").getStr?
             sourceSha256 := ← (← getField j "source_sha256").getStr?
             module := ← parseModule (← getField j "module")
             leanBlocks := ← (← (← getField j "lean_blocks").getArr?).mapM parseLeanBlock }

/-- Convenience: JSON text → `Envelope` (pure; composes `Lean.Json.parse`). -/
def parseEnvelopeString (s : String) : Except String Envelope :=
  Json.parse s >>= parseEnvelope

/-! ## Inline test: the worked `add.py` example from docs/envelope-schema.md -/

/-- The worked `add.py` envelope from the schema doc (sha256 is a placeholder;
the parser does not validate it). -/
private def addEnvelopeText : String := r#"{
  "schema_version": "0.1",
  "language": "python",
  "frontend": {"name": "cpython-ast", "version": "3.9.25"},
  "source_file": "Examples/python/add/add.py",
  "source_sha256": "0000000000000000000000000000000000000000000000000000000000000000",
  "module": {
    "kind": "Module",
    "body": [
      {
        "kind": "FunctionDef",
        "span": {"lineno": 1, "col_offset": 0, "end_lineno": 2, "end_col_offset": 16},
        "name": "add",
        "args": [
          {"arg": "a", "span": {"lineno": 1, "col_offset": 8, "end_lineno": 1, "end_col_offset": 9}},
          {"arg": "b", "span": {"lineno": 1, "col_offset": 11, "end_lineno": 1, "end_col_offset": 12}}
        ],
        "args_unsupported": null,
        "body": [
          {
            "kind": "Return",
            "span": {"lineno": 2, "col_offset": 4, "end_lineno": 2, "end_col_offset": 16},
            "value": {
              "kind": "BinOp",
              "span": {"lineno": 2, "col_offset": 11, "end_lineno": 2, "end_col_offset": 16},
              "left": {"kind": "Name", "span": {"lineno": 2, "col_offset": 11, "end_lineno": 2, "end_col_offset": 12}, "id": "a"},
              "op": "Add",
              "right": {"kind": "Name", "span": {"lineno": 2, "col_offset": 15, "end_lineno": 2, "end_col_offset": 16}, "id": "b"}
            }
          }
        ]
      }
    ]
  },
  "lean_blocks": []
}"#

/-- Structural expectations on the parsed `add.py` envelope: one function
named `"add"` with two plain params `a b`, body `Return (BinOp Add a b)`. -/
private def addEnvelopeChecks : Bool :=
  match parseEnvelopeString addEnvelopeText with
  | .error _ => false
  | .ok env =>
    env.schemaVersion == "0.1" &&
    env.language == "python" &&
    env.sourceFile == "Examples/python/add/add.py" &&
    env.module.topLevel.isEmpty &&
    env.leanBlocks.isEmpty &&
    (match env.module.functions.toList with
      | [f] =>
        f.name == "add" && f.argsOk &&
        (match f.params.toList with
          | [p, q] => p.arg == "a" && q.arg == "b"
          | _ => false) &&
        (match f.body.toList with
          | [.ret (some (.binOp (.name "a" _) .add (.name "b" _) _)) _] => true
          | _ => false)
      | _ => false)

#guard addEnvelopeChecks

end LeanModels.Python
