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
  | "LShift" => .ok .lshift
  | "BitOr" => .ok .bitOr
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
  | "Is" => .ok .is
  | "IsNot" => .ok .isNot
  | "In" => .ok .inOp
  | "NotIn" => .ok .notIn
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
        -- H6: structured plain named keywords. Absent field = empty
        -- (envelopes extracted before the tier stay valid).
        let kwargs ← match j.getObjVal? "keywords" with
          | .error _ => pure #[]
          | .ok kj => do
            (← kj.getArr?).mapM fun kw => do
              let name ← (← getField kw "arg").getStr?
              let value ← parseExpr (← getField kw "value")
              return (name, value)
        let cu ← getOptStrField j "call_unsupported"
        return .call func args kwargs cu span
    | "List" =>
        return .list (← (← (← getField j "elts").getArr?).mapM parseExpr) span
    | "Tuple" =>
        return .tuple (← (← (← getField j "elts").getArr?).mapM parseExpr) span
    | "Dict" =>
        return .dict (← (← (← getField j "keys").getArr?).mapM parseExpr)
          (← (← (← getField j "values").getArr?).mapM parseExpr) span
    | "Attribute" =>
        return .attribute (← parseExpr (← getField j "value"))
          (← (← getField j "attr").getStr?) span
    | "IfExp" =>
        return .ifExp (← parseExpr (← getField j "test"))
          (← parseExpr (← getField j "body"))
          (← parseExpr (← getField j "orelse")) span
    | "Subscript" =>
        let value ← parseExpr (← getField j "value")
        let index ← parseExpr (← getField j "index")
        return .subscript value index span
    | "Slice" =>
        -- Absent components become `Constant None`: CPython compiles a
        -- missing bound to exactly that (`BUILD_SLICE` pushes `None`), so
        -- `s[:i]` and `s[None:i:None]` are the same program, faithfully.
        let value ← parseExpr (← getField j "value")
        let comp : String → Except String Expr := fun name =>
          match j.getObjVal? name with
          | .ok jc => parseExpr jc
          | .error _ => pure (Expr.constant .none span)
        return .slice value (← comp "lower") (← comp "upper") (← comp "step") span
    | "GeneratorExp" | "ListComp" =>
        -- Structured only (H4); `parseModule` LOWERS every surviving
        -- occurrence into a synthesized generator function.
        --
        -- A LIST COMPREHENSION (2026-08-13) is the SAME node under a
        -- different `kind`, desugared here into `list(<the genexp>)`.
        -- That is CPython-exact — both compile to an implicit function
        -- over the already-evaluated outer iterator, and building the
        -- list eagerly from the lazy one observes the same effects in
        -- the same order, because the drain completes before the
        -- enclosing frame can run again. It also inherits the genexp
        -- lowering whole: the capture census, the walrus filter, and
        -- the `drainOk` gate, which already counts `list` as a draining
        -- builtin.
        let elt ← parseExpr (← getField j "elt")
        let target ← parseExpr (← getField j "target")
        let iter ← parseExpr (← getField j "iter")
        let ifs ← (← (← getField j "ifs").getArr?).mapM parseExpr
        -- pass 7 (§the walrus filter): optional filter-bound names, each
        -- `v = <value>` a statement of the synthesized body
        let walrus ← match j.getObjVal? "walrus" with
          | .ok wj => do
            (← wj.getArr?).mapM fun w => do
              pure ((← (← getField w "name").getStr?), ← parseExpr (← getField w "value"))
          | .error _ => pure #[]
        let g := Expr.genExp elt target iter ifs walrus span
        if kind == "ListComp" then
          return .call (.name "list" span) #[g] #[] Option.none span
        else
          return g
    | "Unsupported" =>
        return .unsupported (← (← getField j "py_kind").getStr?)
          (← (← getField j "text").getStr?) span
    | other => throw s!"unknown expression kind {other.quote}"

/-- Parse a statement node (see `parseExpr` for why `partial`). -/
def parseParam (j : Json) : Except String Param :=
  withCtx "param" do
    let default ← match j.getObjVal? "default" with
      | .error _ => pure (Option.none : Option Const)  -- absent: no default
      | .ok .null => pure Option.none
      | .ok v => do pure (some (← parseConst v))
    return { arg := ← (← getField j "arg").getStr?
             span := ← parseSpan (← getField j "span")
             default }

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
    | "For" =>
        return .forStmt (← parseExpr (← getField j "target"))
          (← parseExpr (← getField j "iter"))
          (← (← (← getField j "body").getArr?).mapM parseStmt)
          (← (← (← getField j "orelse").getArr?).mapM parseStmt) span
    | "If" =>
        return .ifStmt (← parseExpr (← getField j "test"))
          (← (← (← getField j "body").getArr?).mapM parseStmt)
          (← (← (← getField j "orelse").getArr?).mapM parseStmt) span
    | "Expr" =>
        return .exprStmt (← parseExpr (← getField j "value")) span
    | "Yield" =>
        -- A bare `yield` carries no "value": ingestion fills `Constant
        -- None`, CPython's own compilation (the `Slice` convention).
        let value ← match j.getObjVal? "value" with
          | .ok jv => parseExpr jv
          | .error _ => pure (Expr.constant .none span)
        return .yieldStmt value span
    | "YieldFrom" =>
        -- pass 5: structured always; `lowerGenExps` inlines the admitted
        -- genexp shape (docs/memory-model.md §yield from), and whatever
        -- survives un-lowered refuses loudly at execution.
        return .yieldFromStmt (← parseExpr (← getField j "value")) span
    | "Raise" =>
        -- exceptions tier: structured in full generality (absent fields
        -- = the bare forms); evaluation owns the tier boundary.
        let exc ← match j.getObjVal? "exc" with
          | .ok jv => do pure (some (← parseExpr jv))
          | .error _ => pure Option.none
        let cause ← match j.getObjVal? "cause" with
          | .ok jv => do pure (some (← parseExpr jv))
          | .error _ => pure Option.none
        return .raiseStmt exc cause span
    | "Assert" =>
        -- the tail batch: `msg` absent is the bare `assert test`
        let msg ← match j.getObjVal? "msg" with
          | .ok jv => do pure (some (← parseExpr jv))
          | .error _ => pure Option.none
        return .assertStmt (← parseExpr (← j.getObjVal? "test")) msg span
    | "Try" =>
        -- exceptions tier: the v0 single-handler fields plus the
        -- `callUnsupported`-style reason (structured-but-loud).
        let body ← (← (← getField j "body").getArr?).mapM parseStmt
        let excName := ((← getField j "exc_name").getStr?).toOption.getD ""
        let handler ← (← (← getField j "handler").getArr?).mapM parseStmt
        let tu ← getOptStrField j "try_unsupported"
        return .tryStmt body excName handler tu span
    | "Pass" => return .pass span
    | "Break" => return .brk span
    | "Continue" => return .cont span
    | "Unsupported" =>
        return .unsupported (← (← getField j "py_kind").getStr?)
          (← (← getField j "text").getStr?) span
    | "FunctionDef" =>
        -- A def NOT directly in a function body (module-level ones are
        -- split out by `parseModule`; direct children of a function body
        -- arrive as "NestedDef"). Representation coverage: keep
        -- ingestion total, mark it unsupported.
        let name := ((← getField j "name").getStr?).toOption.getD ""
        return .unsupported "FunctionDef" name span
    | "NestedDef" =>
        -- H7 (docs/memory-model.md §nested defs and closures): a def
        -- DIRECTLY inside a function body. The snapshot tier's admission
        -- was decided at EXTRACTION — a non-null `closure_unsupported`
        -- keeps the loud refusal, reason attached.
        let name := ((← getField j "name").getStr?).toOption.getD ""
        match ← getOptStrField j "closure_unsupported" with
        | some reason =>
            return .unsupported "NestedDef" s!"{name}: {reason}" span
        | Option.none =>
          let params ← (← (← getField j "args").getArr?).mapM parseParam
          let argsUnsupported ← getOptStrField j "args_unsupported"
          let localsUnsupported ← getOptStrField j "locals_unsupported"
          let hasGlobal := match j.getObjVal? "has_global" with
            | .ok (.bool b) => b
            | _ => false
          let isGenerator := match j.getObjVal? "is_generator" with
            | .ok (.bool b) => b
            | _ => false
          let body ← (← (← getField j "body").getArr?).mapM parseStmt
          let captures ← (← (← getField j "captures").getArr?).mapM (·.getStr?)
          return .defStmt name params argsUnsupported.isNone
            localsUnsupported.isNone hasGlobal isGenerator body captures span
    | "ClassDef" =>
        -- Nested `class` (module-level ones are split out by `parseModule`).
        let name := ((← getField j "name").getStr?).toOption.getD ""
        return .unsupported "ClassDef" name span
    | other => throw s!"unknown statement kind {other.quote}"

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
    let hasGlobal := match j.getObjVal? "has_global" with
      | .ok (.bool b) => b
      | _ => false
    let isGenerator := match j.getObjVal? "is_generator" with
      | .ok (.bool b) => b
      | _ => false
    let body ← (← (← getField j "body").getArr?).mapM parseStmt
    return { name, params, argsOk := argsUnsupported.isNone,
             localsOk := localsUnsupported.isNone, hasGlobal, isGenerator,
             body, span }

/-! ## namedtuple recognition (H3+, docs/memory-model.md §class semantics)

The recorded VALUE-like decision needs `X = namedtuple("T", <fields>)` at
module level to become a `NamedTupleDefn` — a DESUGARING done here, at
ingestion, exactly like the ClassDef method flattening above. It fires
only under conditions that make it provably faithful, ALL-OR-NOTHING per
module; anything else leaves the module byte-identical (the assign stays
an ordinary statement → poisoned G1 binding → loud, never wrong):

1. the EXACT benign import `from collections import namedtuple` is
   present (as the extractor's `Unsupported "ImportFrom"` text);
2. every candidate `X = namedtuple("T", <fields>)` has a valid typename
   and validated field names (CPython's identifier/keyword/underscore/
   duplicate rules — an invalid spec fails the CPython import itself, so
   refusing recognition keeps the loud path);
3. a conservative BINDING CENSUS proves `X` is bound exactly once at top
   level and `namedtuple` is bound only by the benign import: every
   top-level statement must be census-analyzable (structured binds,
   simple one-name imports), no def/class subtree may contain a `global`
   statement (the extractor-recorded `has_global` — exact, nested scopes
   included, so opaque `try`/`with` bodies need no conservative refusal),
   and the name `namedtuple` must not be referenced outside the
   recognized assigns.

On success the benign import and the recognized assigns are replaced by
`pass` (span-preserving): their entire semantics lives in the table —
G1 neither binds nor poisons `X`, and the leanpy prefix/suffix split is
undisturbed. -/

/-- CPython 3.9 keywords (`keyword.kwlist`). -/
private def pyKeywords : List String :=
  ["False", "None", "True", "and", "as", "assert", "async", "await",
   "break", "class", "continue", "def", "del", "elif", "else", "except",
   "finally", "for", "from", "global", "if", "import", "in", "is",
   "lambda", "nonlocal", "not", "or", "pass", "raise", "return", "try",
   "while", "with", "yield"]

/-- ASCII identifier shape (the fragment namedtuple field specs use). -/
private def isPyIdent (s : String) : Bool :=
  match s.toList with
  | [] => false
  | c :: rest => (c.isAlpha || c == '_') && rest.all fun d => d.isAlphanum || d == '_'

/-- A valid namedtuple FIELD name: identifier, not a keyword, no leading
underscore (CPython rejects it without `rename=True` — keyword-only, so
such calls never reach recognition anyway). -/
private def validFieldName (s : String) : Bool :=
  isPyIdent s && !pyKeywords.contains s && !s.startsWith "_"

/-- Split on whitespace AND commas, dropping empties (CPython's
`field_names.replace(',', ' ').split()`). Char-level, toolchain-stable. -/
private def splitWsAux : List Char → List Char → List String
  | [], acc => if acc.isEmpty then [] else [String.ofList acc.reverse]
  | c :: rest, acc =>
    if c.isWhitespace || c == ',' then
      (if acc.isEmpty then [] else [String.ofList acc.reverse]) ++ splitWsAux rest []
    else splitWsAux rest (c :: acc)

@[inherit_doc splitWsAux]
private def splitWs (s : String) : List String := splitWsAux s.toList []

/-- Parse a namedtuple field spec: a string (commas become spaces, then
whitespace-split — CPython's own rule) or a list/tuple of string
literals. `none` = out of the recognized shape. -/
private def parseFieldSpec : Expr → Option (List String)
  | .constant (.str s) _ => some (splitWs s)
  | .list es _ | .tuple es _ =>
    es.toList.mapM fun e =>
      match e with
      | .constant (.str f) _ => some f
      | _ => Option.none
  | _ => Option.none

/-- No duplicate field names (CPython rejects duplicates). -/
private def nodupFields : List String → Bool
  | [] => true
  | f :: fs => !fs.contains f && nodupFields fs

/-- The validated call shape `namedtuple("T", <fields>)` — shared by the
top-level assign candidates and the class-base candidates
(`class Position(namedtuple(…))`). `bindName` is the name constructor
callers resolve (the assigned name, resp. the CLASS name — CPython
instances of the subclass carry the SUBCLASS type). -/
private def ntupleCallSpec (bindName : String) (sp : Span) :
    Expr → Option NamedTupleDefn
  | .call (.name "namedtuple" _) args #[] Option.none _ =>
    match args.toList with
    | [.constant (.str tname) _, fldE] =>
      match parseFieldSpec fldE with
      | some fields =>
        if isPyIdent tname && !pyKeywords.contains tname
            && fields.all validFieldName && nodupFields fields then
          some { name := bindName, tname, fields := fields.toArray, span := sp }
        else Option.none
      | Option.none => Option.none
    | _ => Option.none
  | _ => Option.none

/-- A recognition candidate: `X = namedtuple("T", <fields>)` with a
keyword-free call and a fully validated spec. -/
private def ntCandidate : Stmt → Option NamedTupleDefn
  | .assign tgts rhs sp =>
    (match tgts.toList with
     | [.name x _] => ntupleCallSpec x sp rhs
     | _ => Option.none)
  | _ => Option.none

/-- The exact benign import whose only effect (binding `namedtuple`) the
recognition absorbs — the `namedtuple` row of the shared exact-import
whitelist (`benignImportBinds`, Ast.lean; G1 reads the same table). -/
private def isBenignNtImport : Stmt → Bool
  | .unsupported "ImportFrom" text _ =>
    (benignImportBinds text).map Prod.fst == some "namedtuple"
  | _ => false

/-- Names an assignment-like TARGET binds; `none` = unanalyzable shape.
Subscript/attribute targets bind no name. -/
private def targetBinds : Expr → Option (List String)
  | .name id _ => some [id]
  | .tuple es _ | .list es _ =>
    es.toList.mapM fun e =>
      match e with
      | .name id _ => some id
      | _ => Option.none
  | .subscript .. => some []
  | .attribute .. => some []
  | _ => Option.none

/-- Names a simple import statement's TEXT binds (`from A import B` binds
`B`; `import A.B` binds `A`); `none` = not a simple single-name import. -/
private def importBinds (text : String) : Option (List String) :=
  if (text.splitOn ",").length != 1 || (text.splitOn " as ").length != 1 then
    Option.none
  else
    match splitWs text with
    | ["from", _, "import", n] => if isPyIdent n then some [n] else Option.none
    | ["import", m] =>
      match (m.splitOn ".").head? with
      | some root => if isPyIdent root then some [root] else Option.none
      | Option.none => Option.none
    | _ => Option.none

/-- Names a top-level statement (nested included) can bind; `none` =
unanalyzable (refuses the whole recognition). -/
private partial def stmtBinds : Stmt → Option (List String)
  | .assign tgts _ _ => do
    let bss ← tgts.toList.mapM targetBinds
    return bss.flatten
  | .augAssign t _ _ _ => targetBinds t
  | .forStmt t _ body orelse _ => do
    let tb ← targetBinds t
    let bb ← body.toList.mapM stmtBinds
    let ob ← orelse.toList.mapM stmtBinds
    return tb ++ bb.flatten ++ ob.flatten
  | .whileLoop _ body orelse _ | .ifStmt _ body orelse _ => do
    let bb ← body.toList.mapM stmtBinds
    let ob ← orelse.toList.mapM stmtBinds
    return bb.flatten ++ ob.flatten
  | .ret .. | .exprStmt .. | .yieldStmt .. | .pass _ | .brk _ | .cont _ => some []
  -- pass 5: impossible at module top level (CPython parse error) —
  -- unanalyzable, conservative
  | .yieldFromStmt .. => Option.none
  -- H7: a nested def binds its NAME; the body is its own scope
  | .defStmt name _ _ _ _ _ _ _ _ => some [name]
  -- exceptions tier: `raise` binds nothing; a try can bind whatever its
  -- body and handler can (over-approximation, the safe direction)
  | .raiseStmt .. => some []
  | .assertStmt .. => some []
  | .tryStmt b _ hnd _ _ => do
    let bb ← b.toList.mapM stmtBinds
    let hb ← hnd.toList.mapM stmtBinds
    return bb.flatten ++ hb.flatten
  | .unsupported "ImportFrom" text _ => importBinds text
  | .unsupported "Import" text _ => importBinds text
  | .unsupported .. => Option.none

mutual
  /-- Every `Name` occurring in the expression (the reference scan). -/
  private partial def exprRefs : Expr → List String
    | .constant .. => []
    | .name id _ => [id]
    | .binOp l _ r _ => exprRefs l ++ exprRefs r
    | .unaryOp _ e _ => exprRefs e
    | .boolOp _ vs _ => (vs.toList.map exprRefs).flatten
    | .compare l _ cs _ => exprRefs l ++ (cs.toList.map exprRefs).flatten
    | .call f args kwargs _ _ =>
      exprRefs f ++ (args.toList.map exprRefs).flatten
        ++ (kwargs.toList.map (fun kv => exprRefs kv.2)).flatten
    | .list es _ | .tuple es _ => (es.toList.map exprRefs).flatten
    | .subscript v i _ => exprRefs v ++ exprRefs i
    | .dict ks vs _ => (ks.toList.map exprRefs).flatten ++ (vs.toList.map exprRefs).flatten
    | .attribute v _ _ => exprRefs v
    | .ifExp t b o _ => exprRefs t ++ exprRefs b ++ exprRefs o
    | .slice v l u st _ => exprRefs v ++ exprRefs l ++ exprRefs u ++ exprRefs st
    | .genExp e t it ifs wb _ =>
      exprRefs e ++ exprRefs t ++ exprRefs it ++ (ifs.toList.map exprRefs).flatten
        ++ (wb.toList.map (fun p => exprRefs p.2)).flatten
    | .unsupported .. => []

  /-- Every `Name` occurring in the statement. -/
  private partial def stmtRefs : Stmt → List String
    | .ret Option.none _ => []
    | .ret (some e) _ => exprRefs e
    | .assign tgts v _ => (tgts.toList.map exprRefs).flatten ++ exprRefs v
    | .augAssign t _ v _ => exprRefs t ++ exprRefs v
    | .whileLoop t b o _ | .ifStmt t b o _ =>
      exprRefs t ++ (b.toList.map stmtRefs).flatten ++ (o.toList.map stmtRefs).flatten
    | .forStmt t it b o _ =>
      exprRefs t ++ exprRefs it ++ (b.toList.map stmtRefs).flatten
        ++ (o.toList.map stmtRefs).flatten
    | .exprStmt e _ => exprRefs e
    | .yieldStmt e _ => exprRefs e
    | .yieldFromStmt v _ => exprRefs v
    | .defStmt _ _ _ _ _ _ body _ _ => (body.toList.map stmtRefs).flatten
    -- exceptions tier: the handler CLASS NAME is a reference too
    | .raiseStmt exc cause _ =>
      (exc.map exprRefs).getD [] ++ (cause.map exprRefs).getD []
    | .assertStmt t m _ =>
      exprRefs t ++ (m.map exprRefs).getD []
    | .tryStmt b excName hnd _ _ =>
      excName :: (b.toList.map stmtRefs).flatten ++ (hnd.toList.map stmtRefs).flatten
    | .pass _ | .brk _ | .cont _ => []
    | .unsupported .. => []
end

/-- The span of a statement (every constructor carries one last). -/
private def stmtSpanOf : Stmt → Span
  | .ret _ sp | .assign _ _ sp | .augAssign _ _ _ sp
  | .whileLoop _ _ _ sp | .forStmt _ _ _ _ sp | .ifStmt _ _ _ sp
  | .exprStmt _ sp | .yieldStmt _ sp | .yieldFromStmt _ sp
  | .pass sp | .brk sp | .cont sp
  | .defStmt _ _ _ _ _ _ _ _ sp
  | .raiseStmt _ _ sp | .tryStmt _ _ _ _ sp | .assertStmt _ _ sp
  | .unsupported _ _ sp => sp

/-- The recognition pass (see the section comment for the rules). Returns
the module's top level with the benign import and every recognized assign
replaced by `pass`, plus the namedtuple table — or the input unchanged
(all-or-nothing: partial recognition could leave a stray `namedtuple`
reference resolving to a wrong `NameError`). -/
private def recognizeNamedtuples (functions : Array FunctionDefn)
    (classes : Array ClassDefn) (topLevel : Array Stmt) :
    Array Stmt × Array NamedTupleDefn × Array ClassDefn :=
  -- demotion restores the loud inheritance state for every class-base
  -- CANDIDATE (parseClassDefn stores them unconditionally)
  let demoted := classes.map fun c =>
    if c.ntBase.isSome then
      { c with ntBase := Option.none, ok := false, creationPure := false } else c
  let unchanged := (topLevel, #[], demoted)
  -- rule 1: the benign import is present
  if !topLevel.any isBenignNtImport then unchanged else
  -- candidates, in source order (assign binds and class bases share the
  -- census — a failed census demotes BOTH, all-or-nothing)
  let cands := topLevel.toList.filterMap ntCandidate
  if cands.isEmpty && !classes.any (·.ntBase.isSome) then unchanged else
  -- rule 3a: the census must analyze EVERY top-level statement
  match (topLevel.toList.filter (!isBenignNtImport ·)).mapM stmtBinds with
  | Option.none => unchanged
  | some bindss =>
    let bound := bindss.flatten
    -- rule 3b: no def/class subtree may leak a module binding (`global` —
    -- the EXACT extractor-recorded fact `has_global`, nested scopes and
    -- opaque statements included, so `try`/`with` need no conservative
    -- refusal)
    if functions.any (·.hasGlobal) || classes.any (·.hasGlobal) then unchanged else
    -- rule 3c: `namedtuple` is bound only by the benign import and
    -- referenced only inside the candidate assigns
    let fnames := functions.toList.map FunctionDefn.name
    let cnames := classes.toList.map ClassDefn.name
    if bound.contains "namedtuple" || fnames.contains "namedtuple"
        || cnames.contains "namedtuple" then unchanged else
    let tlRefs :=
      ((topLevel.toList.filter (fun s => (ntCandidate s).isNone)).map stmtRefs).flatten
    let fnRefs :=
      (functions.toList.map (fun f => (f.body.toList.map stmtRefs).flatten)).flatten
    if (tlRefs ++ fnRefs).contains "namedtuple" then unchanged else
    -- per-candidate: X bound exactly once (its own assign), no def/class X.
    -- ALL-OR-NOTHING: one rejected candidate refuses the whole pass.
    let ok := cands.all fun nt =>
      (bound.filter (· == nt.name)).length == 1
        && !fnames.contains nt.name && !cnames.contains nt.name
        && (cands.filter (fun nt' => nt'.name == nt.name)).length == 1
    if !ok then unchanged else
    -- class-base candidates: the class name must not collide with an
    -- assign candidate, a top-level bind, or another same-named class
    -- (the def/class collision guard already covers `def`s loudly)
    let cok := classes.all fun c =>
      c.ntBase.isNone ||
        (!bound.contains c.name
          && (cands.all fun nt => nt.name != c.name)
          && (classes.toList.filter (fun c' => c'.name == c.name)).length == 1)
    if !cok then unchanged else
    -- IDENTITY of method dispatch: a plain candidate's TYPENAME may not
    -- collide with an `ntBase` class's NAME — otherwise a plain value
    -- would carry a tname that names the subclass and dispatch its
    -- methods (CPython: unrelated classes, AttributeError)
    let tnameClash := cands.any fun nt =>
      classes.any fun c => c.ntBase.isSome && c.name == nt.tname
    if tnameClash then unchanged else
    let topLevel' := topLevel.map fun s =>
      if isBenignNtImport s || (ntCandidate s).isSome then .pass (stmtSpanOf s)
      else s
    (topLevel', cands.toArray, classes)

/-- Can this class-body statement change anything observable when CPython
executes the class body? `pass`, a docstring (or stray constant), a method,
and an attribute bound to a LITERAL are all invisible: the model skips
class creation entirely, and skipping these skips nothing. Anything that
calls, reads a name, subscripts, or loops can print or raise at exactly the
`class` statement, where the model does nothing at all — so it is NOT pure
and `runScript` refuses the module (`ClassDefn.creationPure`). -/
def classBodyStmtPure (s : Stmt) : Bool :=
  match s with
  | .pass _ => true
  | .exprStmt (.constant _ _) _ => true
  | .assign targets (.constant _ _) _ =>
      targets.all fun t => match t with | .name _ _ => true | _ => false
  | .defStmt .. => true
  | _ => false

/-- Parse a module-level `ClassDef` node (H3): the `ClassDefn` record plus
the method `FunctionDefn`s FLATTENED under qualified names
`"<class>.<method>"` (see `ClassDefn`'s docstring — method calls reuse
`callIn` verbatim). `ok` is `true` iff `class_unsupported` is `null`
(bases/keywords/decorators/class-level statements set it at extraction).
Non-`FunctionDef` body statements are dropped here — they already set
`class_unsupported`, so no instance of the class can ever be built. -/
def parseClassDefn (j : Json) : Except String (ClassDefn × Array FunctionDefn) :=
  withCtx "ClassDef" do
    let name ← (← getField j "name").getStr?
    let span ← parseSpan (← getField j "span")
    let classUnsupported ← getOptStrField j "class_unsupported"
    let hasGlobal := match j.getObjVal? "has_global" with
      | .ok (.bool b) => b
      | _ => false
    -- the structured namedtuple BASE (extractor: a single plain
    -- `namedtuple(…)` base) — a CANDIDATE here; `recognizeNamedtuples`
    -- promotes it (module census) or demotes the class to the ordinary
    -- uninstantiable-loudly state. The inner `name` is the CLASS name:
    -- CPython instances carry the SUBCLASS type.
    let ntBase ← match j.getObjVal? "namedtuple_base" with
      | .error _ => pure (Option.none : Option NamedTupleDefn)
      | .ok .null => pure Option.none
      | .ok baseJson => do
        pure (ntupleCallSpec name span (← parseExpr baseJson))
    -- the exceptions tier's THIRD class kind (docs/memory-model.md
    -- §exceptions): the extractor marks the exact `class N(Exception):
    -- pass` shape; a CANDIDATE here — `parseModule`'s census demotes it
    -- (isExc := false, ok := false) unless `Exception` is provably
    -- unshadowed at module level (the ntBase demotion discipline).
    let isExc := match j.getObjVal? "exception_base" with
      | .ok (.bool b) => b
      | _ => false
    let body ← (← getField j "body").getArr?
    let mut methods : Array String := #[]
    let mut fns : Array FunctionDefn := #[]
    for stmtJson in body do
      let k ← (← getField stmtJson "kind").getStr?
      if k == "FunctionDef" then
        let f ← parseFunctionDefn stmtJson
        methods := methods.push f.name
        fns := fns.push { f with name := name ++ "." ++ f.name }
    -- CREATION PURITY (docs/memory-model.md §class creation): the
    -- extractor's structured verdict, re-checked here over the parsed body
    -- so ingestion never trusts a field it can verify. An envelope from
    -- before the field existed has no verdict, and the safe answer is the
    -- LOUD one.
    let noCreationEffects := match j.getObjVal? "creation_effects" with
      | .ok (.bool b) => !b
      | _ => false
    let bodyPure ← body.allM fun stmtJson => do
      let k ← (← getField stmtJson "kind").getStr?
      if k == "FunctionDef" then pure true else pure (classBodyStmtPure (← parseStmt stmtJson))
    return ({ name, ok := classUnsupported.isNone, methods, hasGlobal, ntBase,
              isExc, creationPure := noCreationEffects && bodyPure, span }, fns)

/-! ## Generator-expression lowering (H4, docs/memory-model.md
§generator semantics)

CPython compiles `(elt for t in it if c)` into an implicit generator
FUNCTION whose FIRST argument is the already-evaluated outer iterator
(`MAKE_FUNCTION <genexpr>; …; GET_ITER; CALL_FUNCTION 1`), and this pass
performs exactly that lowering, at ingestion, so genexps ride the same
machinery as every other generator — no second evaluation story.

The one real design point is CAPTURE. CPython closes over the enclosing
frame BY REFERENCE; a lowering that passes free names as extra arguments
captures them BY VALUE, and the two disagree exactly when a captured
name is REBOUND between the genexp's creation and its consumption. v0
therefore admits a free name only when the two provably agree:

* it is a PARAMETER of the enclosing function that the body never
  assigns (bound once, at the call — by-value is by-reference), or
* it is resolved outside the frame anyway: a module-level binding
  (`piece`, `MATE_UPPER`, a `def`/`class`/namedtuple name) or a builtin,
  neither of which is captured at all.

Anything else — a local the body assigns, an unanalyzable target —
leaves the `Expr.genExp` node in place, and EVALUATING it refuses
loudly (Semantics.lean). Never a silent by-value guess. -/

/-- Builtin names the lowering must not treat as captures. Deliberately
a LOCAL list rather than an import of `isBuiltinName` (Semantics.lean
imports nothing from here and this file imports only the AST): a name
missing from it costs a loud refusal, never a wrong capture, so the two
lists may drift safely in the only direction that matters. -/
private def lowerBuiltins : List String :=
  ["len", "sorted", "max", "min", "abs", "int", "print", "ord", "chr",
   "next", "range", "enumerate", "count", "all", "any", "sum", "tuple",
   "list", "dict", "str", "bool", "set", "reversed", "zip", "map",
   "filter", "True", "False", "None"]

/-- Builtins that DRAIN a directly-passed genexp within the enclosing
elt evaluation (the `genTargets` admission's gate — pass 3). -/
private def drainingBuiltins : List String :=
  ["tuple", "sum", "sorted", "max", "min", "any", "all", "list", "set"]

/-- The synthesized name of a lowered generator expression. CPython calls
the implicit function `<genexpr>`; the index keeps several genexps in one
module apart, and the angle brackets make collision with a real Python
identifier impossible. -/
def genExpName (n : Nat) : String := s!"<genexpr@{n}>"

/-- CPython's own name for the implicit first parameter (the
already-evaluated outer iterator). No Python identifier contains `.`. -/
def genExpArg : String := ".0"

/-- Wrap a statement in the genexp's filters, innermost last:
`if c₁: if c₂: <stmt>`. -/
private def guardWith (sp : Span) : List Expr → Stmt → Stmt
  | [], body => body
  | c :: cs, body => .ifStmt c #[guardWith sp cs body] #[] sp

/-- Deduplicate, keeping first occurrence. -/
private def dedup (l : List String) : List String :=
  l.foldl (init := []) (fun acc n => if acc.contains n then acc else acc ++ [n])

/-- Names a function body assigns anywhere (CPython's static-locals
rule), over-approximated: an unanalyzable target contributes nothing but
also cannot hide a name that `targetBinds` would have found, so the
capture test stays conservative in the safe direction — an unnoticed
rebinding is impossible for the shapes `targetBinds` analyses, and every
other shape binds nothing. -/
private partial def bodyAssigns : Stmt → List String
  | .assign ts _ _ => (ts.toList.map (fun t => (targetBinds t).getD [])).flatten
  | .augAssign t _ _ _ => (targetBinds t).getD []
  | .forStmt t _ b o _ =>
      (targetBinds t).getD [] ++ (b.toList.map bodyAssigns).flatten
        ++ (o.toList.map bodyAssigns).flatten
  | .whileLoop _ b o _ | .ifStmt _ b o _ =>
      (b.toList.map bodyAssigns).flatten ++ (o.toList.map bodyAssigns).flatten
  -- H7: the def NAME becomes a local of the enclosing body; the nested
  -- BODY is its own scope and contributes nothing here
  | .defStmt name _ _ _ _ _ _ _ _ => [name]
  -- exceptions tier: body and handler assigns both count
  | .tryStmt b _ hnd _ _ =>
      (b.toList.map bodyAssigns).flatten ++ (hnd.toList.map bodyAssigns).flatten
  | _ => []

/-- Every name a statement can OBSERVE or BIND — reads (`exprRefs` of
each embedded expression, targets included: conservative), binding
targets, nested-def names and captures (a capture is the one window a
nested body has into the enclosing frame) — EXCEPT the subtrees of
statement-position `yield from <genexp>` statements, which contribute
NOTHING: the inlining admission (pass 5, docs/memory-model.md §yield
from) asks whether the genexp's target occurs anywhere OUTSIDE
yield-from subtrees, and skipping them ALL lets two yield-froms share
a target soundly (the second loop's rebinding is as unobservable as
the first's binding). -/
private partial def yfNames : Stmt → List String
  | .yieldFromStmt (.genExp ..) _ => []
  | .yieldFromStmt v _ => exprRefs v
  | .ret Option.none _ | .pass _ | .brk _ | .cont _ | .unsupported .. => []
  | .ret (some e) _ => exprRefs e
  | .assign ts v _ =>
      (ts.toList.map exprRefs).flatten
        ++ (ts.toList.map (fun t => (targetBinds t).getD [])).flatten
        ++ exprRefs v
  | .augAssign t _ v _ => exprRefs t ++ (targetBinds t).getD [] ++ exprRefs v
  | .whileLoop t b o _ =>
      exprRefs t ++ (b.toList.map yfNames).flatten ++ (o.toList.map yfNames).flatten
  | .forStmt t it b o _ =>
      exprRefs t ++ (targetBinds t).getD [] ++ exprRefs it
        ++ (b.toList.map yfNames).flatten ++ (o.toList.map yfNames).flatten
  | .ifStmt t b o _ =>
      exprRefs t ++ (b.toList.map yfNames).flatten ++ (o.toList.map yfNames).flatten
  | .exprStmt e _ => exprRefs e
  | .yieldStmt e _ => exprRefs e
  | .raiseStmt exc cause _ =>
      (exc.map exprRefs).getD [] ++ (cause.map exprRefs).getD []
  | .assertStmt t m _ =>
      exprRefs t ++ (m.map exprRefs).getD []
  | .tryStmt b _ hnd _ _ =>
      (b.toList.map yfNames).flatten ++ (hnd.toList.map yfNames).flatten
  | .defStmt name _ _ _ _ _ body captures _ =>
      [name] ++ captures.toList ++ (body.toList.map yfNames).flatten

/-- Direct-child bindings of a function body with their line numbers
(`LowerCtx.boundBefore` — see its docstring for the admission this
feeds). Only shapes whose binding provably executes when reached:
single-target name/tuple assigns and nested defs, DIRECTLY in the body
(never inside a nested `if`/loop, whose execution is conditional). -/
private def directBinds (body : List Stmt) : List (String × Nat) :=
  body.foldl (init := []) fun acc s =>
    match s with
    | .assign tgts _ sp =>
      (match tgts.toList with
       | [t] => acc ++ ((targetBinds t).getD []).map (fun x => (x, sp.lineno))
       | _ => acc)
    | .defStmt name _ _ _ _ _ _ _ sp => acc ++ [(name, sp.lineno)]
    | _ => acc

/-- What a lowering pass may capture and what it must refuse. -/
private structure LowerCtx where
  /-- Names resolved outside the frame (module bindings + builtins). -/
  outer : List String
  /-- The enclosing function's parameters. -/
  params : List String
  /-- Names the enclosing body assigns anywhere (CPython's static-locals
  rule makes these local throughout, so a parameter listed here is
  REBINDABLE and cannot be captured by value). -/
  assigned : List String
  /-- Targets of ENCLOSING genexps whose elt we are lowering (pass 3 —
  sunfish's K_END nests a genexp inside a genexp's elt). Admissible as
  by-value captures ONLY in immediately-drained position (`drainOk`):
  the drain completes within one elt evaluation, before the enclosing
  target can advance, so by-value equals CPython's by-reference. -/
  genTargets : List String := []
  /-- Names bound by a DIRECT CHILD of the enclosing body (single-target
  assigns, nested defs) with their line numbers (pass 4,
  docs/memory-model.md §bound() end-to-end): under `drainOk` a
  body-ASSIGNED free name is admissible when provably BOUND at the
  genexp's creation — it is a parameter, or a direct-child bind at a
  strictly smaller line (direct children execute in order, so the bind
  ran before any statement containing the genexp). The drain-gate makes
  by-value-at-creation equal CPython's by-reference; boundness is what
  rules out a fake `NameError` on an empty iterable. -/
  boundBefore : List (String × Nat) := []
  /-- pass 5 (docs/memory-model.md §yield from): every name the
  enclosing body reads or binds OUTSIDE yield-from-genexp statements'
  own subtrees (`yfNames`) — the inlining admission's forbidden set for
  the genexp's target. -/
  yfForbidden : List String := []
  /-- pass 7 (docs/memory-model.md §the walrus filter): every name
  occurring in the enclosing body OUTSIDE walrus-bearing-genexp
  subtrees. PEP 572 leaks a comprehension walrus into the enclosing
  frame; the frame-LOCAL lowering is observationally equal only when
  the enclosing body never looks — a walrus name in this set refuses
  the lowering (the genexp stays un-lowered, loud at evaluation). -/
  walrusForbidden : List String := []

/-- pass 7 (docs/memory-model.md §the walrus filter): every name
occurring in the expression OUTSIDE walrus-bearing-genexp subtrees —
reads and binds alike. The skip is what lets the shipped QS line's `v`
live only inside its own genexp; any other occurrence lands in
`walrusForbidden` and refuses the lowering. -/
private partial def exprNamesXW : Expr → List String
  | .constant .. => []
  | .name id _ => [id]
  | .binOp l _ r _ => exprNamesXW l ++ exprNamesXW r
  | .unaryOp _ e _ => exprNamesXW e
  | .boolOp _ vs _ => (vs.toList.map exprNamesXW).flatten
  | .compare l _ cs _ => exprNamesXW l ++ (cs.toList.map exprNamesXW).flatten
  | .call f args kwargs _ _ =>
      exprNamesXW f ++ (args.toList.map exprNamesXW).flatten
        ++ (kwargs.toList.map (fun kv => exprNamesXW kv.2)).flatten
  | .list es _ | .tuple es _ => (es.toList.map exprNamesXW).flatten
  | .subscript v i _ => exprNamesXW v ++ exprNamesXW i
  | .dict ks vs _ =>
      (ks.toList.map exprNamesXW).flatten ++ (vs.toList.map exprNamesXW).flatten
  | .attribute v _ _ => exprNamesXW v
  | .ifExp t b o _ => exprNamesXW t ++ exprNamesXW b ++ exprNamesXW o
  | .slice v l u st _ =>
      exprNamesXW v ++ exprNamesXW l ++ exprNamesXW u ++ exprNamesXW st
  | .genExp e t it ifs wb _ =>
      if wb.isEmpty then
        exprNamesXW e ++ exprNamesXW t ++ exprNamesXW it
          ++ (ifs.toList.map exprNamesXW).flatten
      else []
  | .unsupported .. => []

/-- The statement-level walk for `exprNamesXW` (binds included via the
target expressions themselves — a target `Name` IS a name). -/
private partial def stmtNamesXW : Stmt → List String
  | .ret Option.none _ | .pass _ | .brk _ | .cont _ | .unsupported .. => []
  | .ret (some e) _ => exprNamesXW e
  | .assign ts v _ => (ts.toList.map exprNamesXW).flatten ++ exprNamesXW v
  | .augAssign t _ v _ => exprNamesXW t ++ exprNamesXW v
  | .whileLoop t b o _ | .ifStmt t b o _ =>
      exprNamesXW t ++ (b.toList.map stmtNamesXW).flatten
        ++ (o.toList.map stmtNamesXW).flatten
  | .forStmt t it b o _ =>
      exprNamesXW t ++ exprNamesXW it ++ (b.toList.map stmtNamesXW).flatten
        ++ (o.toList.map stmtNamesXW).flatten
  | .exprStmt e _ | .yieldStmt e _ | .yieldFromStmt e _ => exprNamesXW e
  | .raiseStmt exc cause _ =>
      (exc.map exprNamesXW).getD [] ++ (cause.map exprNamesXW).getD []
  | .assertStmt t m _ =>
      exprNamesXW t ++ (m.map exprNamesXW).getD []
  | .tryStmt b en hnd _ _ =>
      [en] ++ (b.toList.map stmtNamesXW).flatten
        ++ (hnd.toList.map stmtNamesXW).flatten
  | .defStmt name params _ _ _ _ body captures _ =>
      -- a NESTED scope: its walrus rules are its own; conservatively,
      -- every name it mentions counts as an enclosing occurrence
      [name] ++ params.toList.map Param.arg ++ captures.toList
        ++ (body.toList.map stmtNamesXW).flatten

mutual
  /-- Rewrite every lowerable genexp in the expression, bottom up. The
  state is the fresh-name counter and the synthesized functions. -/
  private partial def lowerExpr (ctx : LowerCtx) (e : Expr)
      (drainOk : Bool := false) :
      StateM (Nat × Array FunctionDefn) Expr := do
    match e with
    | .constant .. | .name .. | .unsupported .. => return e
    | .binOp l op r sp => return .binOp (← lowerExpr ctx l) op (← lowerExpr ctx r) sp
    | .unaryOp op v sp => return .unaryOp op (← lowerExpr ctx v) sp
    | .boolOp op vs sp => return .boolOp op (← lowerExprs ctx vs) sp
    | .compare l ops cs sp => return .compare (← lowerExpr ctx l) ops (← lowerExprs ctx cs) sp
    | .call f args kwargs cu sp =>
        -- pass 3: a genexp passed DIRECTLY to a draining builtin may
        -- capture enclosing-genexp targets (`drainOk` — see LowerCtx)
        let drainOk := match f with
          | .name d _ => drainingBuiltins.contains d
          | _ => false
        let args' ← args.mapM fun a => do
          match a with
          | .genExp .. => lowerExpr ctx a (drainOk := drainOk)
          | a => lowerExpr ctx a
        return .call (← lowerExpr ctx f) args'
          (← kwargs.mapM fun kv => do pure (kv.1, ← lowerExpr ctx kv.2)) cu sp
    | .list es sp => return .list (← lowerExprs ctx es) sp
    | .tuple es sp => return .tuple (← lowerExprs ctx es) sp
    | .subscript v i sp => return .subscript (← lowerExpr ctx v) (← lowerExpr ctx i) sp
    | .dict ks vs sp => return .dict (← lowerExprs ctx ks) (← lowerExprs ctx vs) sp
    | .attribute v a sp => return .attribute (← lowerExpr ctx v) a sp
    | .ifExp t b o sp =>
        return .ifExp (← lowerExpr ctx t) (← lowerExpr ctx b) (← lowerExpr ctx o) sp
    | .slice v l u st sp =>
        return .slice (← lowerExpr ctx v) (← lowerExpr ctx l) (← lowerExpr ctx u)
          (← lowerExpr ctx st) sp
    | .genExp elt target iter ifs wb sp => do
      let tb0 := (targetBinds target).getD []
      -- the elt lowers under the grown genTargets (an inner genexp in
      -- immediately-drained position may capture THIS genexp's target)
      let elt ← lowerExpr { ctx with genTargets := ctx.genTargets ++ tb0 } elt
      let iter ← lowerExpr ctx iter
      let ifs ← lowerExprs ctx ifs
      let wb ← wb.mapM fun p => do pure (p.1, ← lowerExpr ctx p.2)
      match targetBinds target with
      | Option.none => return .genExp elt target iter ifs wb sp
      | some tb =>
        -- pass 7 (§the walrus filter): walrus names are LOCALS of the
        -- synthesized frame — they join the bound set for the capture
        -- census, and the admission refuses any walrus name the
        -- enclosing body mentions (`walrusForbidden` — PEP 572 leaks
        -- the binding there, and a frame-local must be unobservable)
        let wbNames := wb.toList.map Prod.fst
        let tb := tb ++ wbNames
        let refs := dedup (exprRefs elt ++ (ifs.toList.map exprRefs).flatten
          ++ (wb.toList.map (fun p => exprRefs p.2)).flatten)
        let caps := refs.filter fun n =>
          !tb.contains n && !ctx.outer.contains n && !lowerBuiltins.contains n
            && n != genExpArg
            -- a synthesized `<genexpr@m>` call inside THIS elt (pass 3:
            -- K_END nests one) resolves through Module.functions — the
            -- leading `<` is unnameable in Python (the defsBeforeLive
            -- precedent), never a capturable frame name
            && !(n.startsWith "<")
        if caps.all (fun n =>
            (ctx.params.contains n && !ctx.assigned.contains n)
              || (drainOk && ctx.genTargets.contains n)
              -- pass 4: body-assigned names under an immediate drain,
              -- provided boundness at creation (see LowerCtx.boundBefore)
              || (drainOk && (ctx.params.contains n
                    || ctx.boundBefore.any (fun p => p.1 == n && p.2 < sp.lineno))))
            && wbNames.all (fun n => !ctx.walrusForbidden.contains n) then
          let (n, fns) ← get
          let fname := genExpName n
          let body : Array Stmt :=
            #[.forStmt target (.name genExpArg sp)
                ((wb.map fun p => Stmt.assign #[.name p.1 sp] p.2 sp)
                  ++ #[guardWith sp ifs.toList (.yieldStmt elt sp)]) #[] sp]
          let params : Array Param :=
            (#[genExpArg] ++ caps.toArray).map fun a => { arg := a, span := sp }
          set (n + 1,
            fns.push { name := fname, params, argsOk := true, localsOk := true,
                       hasGlobal := false, isGenerator := true, body, span := sp })
          return .call (.name fname sp)
            (#[iter] ++ (caps.map (fun c => Expr.name c sp)).toArray) #[] Option.none sp
        else
          return .genExp elt target iter ifs wb sp

  /-- Elementwise `lowerExpr`. -/
  private partial def lowerExprs (ctx : LowerCtx) (es : Array Expr) :
      StateM (Nat × Array FunctionDefn) (Array Expr) :=
    es.mapM (lowerExpr ctx)
end

mutual
  /-- Rewrite every lowerable genexp in the statement. -/
  private partial def lowerStmt (ctx : LowerCtx) (s : Stmt) :
      StateM (Nat × Array FunctionDefn) Stmt := do
    match s with
    | .ret Option.none _ | .pass _ | .brk _ | .cont _ | .unsupported .. => return s
    | .ret (some e) sp => return .ret (some (← lowerExpr ctx e)) sp
    | .assign ts v sp => return .assign (← lowerExprs ctx ts) (← lowerExpr ctx v) sp
    | .augAssign t op v sp => return .augAssign (← lowerExpr ctx t) op (← lowerExpr ctx v) sp
    | .whileLoop t b o sp =>
        return .whileLoop (← lowerExpr ctx t) (← lowerStmts ctx b) (← lowerStmts ctx o) sp
    | .forStmt t it b o sp =>
        return .forStmt (← lowerExpr ctx t) (← lowerExpr ctx it)
          (← lowerStmts ctx b) (← lowerStmts ctx o) sp
    | .ifStmt t b o sp =>
        return .ifStmt (← lowerExpr ctx t) (← lowerStmts ctx b) (← lowerStmts ctx o) sp
    | .exprStmt e sp => return .exprStmt (← lowerExpr ctx e) sp
    | .yieldStmt e sp => return .yieldStmt (← lowerExpr ctx e) sp
    | .yieldFromStmt v sp =>
      (match v with
       | .genExp elt target iter ifs wb gsp => do
        -- pass 5 (docs/memory-model.md §yield from): INLINE the
        -- delegation — `for target in iter: [ifs:] yield elt` — when
        -- the target binds analyzably and its names occur nowhere else
        -- in the enclosing body. The FREE names need no admission at
        -- all: the inlined loop reads the enclosing frame by reference,
        -- which is exactly what a delegated genexp does (the enclosing
        -- frame cannot run mid-delegation). Subexpressions lower first,
        -- as everywhere; an inadmissible shape survives un-lowered and
        -- refuses loudly at execution.
        let elt ← lowerExpr ctx elt
        let iter ← lowerExpr ctx iter
        let ifs ← lowerExprs ctx ifs
        match targetBinds target with
        | some tb =>
          -- pass 7: a walrus-bearing delegation is NOT inlined (its
          -- binding would land in the enclosing frame — representable,
          -- unneeded, refused loudly at evaluation)
          if tb.all (fun n => !ctx.yfForbidden.contains n) && wb.isEmpty then
            return .forStmt target iter
              #[guardWith gsp ifs.toList (.yieldStmt elt gsp)] #[] sp
          else
            return .yieldFromStmt (.genExp elt target iter ifs wb gsp) sp
        | Option.none =>
            return .yieldFromStmt (.genExp elt target iter ifs wb gsp) sp
       | v => do return .yieldFromStmt (← lowerExpr ctx v) sp)
    | .raiseStmt exc cause sp =>
        return .raiseStmt (← exc.mapM (lowerExpr ctx)) (← cause.mapM (lowerExpr ctx)) sp
    | .assertStmt t m sp =>
        return .assertStmt (← lowerExpr ctx t) (← m.mapM (lowerExpr ctx)) sp
    | .tryStmt b en hnd tu sp =>
        return .tryStmt (← lowerStmts ctx b) en (← lowerStmts ctx hnd) tu sp
    | .defStmt name params ao lo hg ig body captures sp =>
        -- H7: the nested body lowers under its OWN ctx. Closure captures
        -- are never-rebound by admission, so a genexp inside the nested
        -- body may capture them BY VALUE exactly like never-assigned
        -- parameters — sunfish's ordering line inside `moves()`.
        let ctx' : LowerCtx :=
          { ctx with
            params := params.toList.map Param.arg ++ captures.toList
            assigned := (body.toList.map bodyAssigns).flatten
            boundBefore := directBinds body.toList
            yfForbidden := (body.toList.map yfNames).flatten
            walrusForbidden := params.toList.map Param.arg ++ captures.toList
              ++ (body.toList.map stmtNamesXW).flatten }
        return .defStmt name params ao lo hg ig (← lowerStmts ctx' body) captures sp

  /-- Elementwise `lowerStmt`. -/
  private partial def lowerStmts (ctx : LowerCtx) (ss : Array Stmt) :
      StateM (Nat × Array FunctionDefn) (Array Stmt) :=
    ss.mapM (lowerStmt ctx)
end

/-- Lower every genexp in the module: function bodies first, then the
TOP LEVEL. A module-scope genexp needs no capture list at all — every
free name it has is a module global, which the synthesized function
resolves through the same static table (module bindings are immutable in
tier, the standing G1 assumption, so by-value and by-reference agree
there by construction). Returns the rewritten functions and top level
PLUS the synthesized generator functions, in creation order. -/
private def lowerGenExps (outer : List String) (functions : Array FunctionDefn)
    (topLevel : Array Stmt) : Array FunctionDefn × Array Stmt :=
  let step := functions.foldl (init := (#[], (0, (#[] : Array FunctionDefn))))
    fun (acc, st) f =>
      let ctx : LowerCtx :=
        { outer
          params := f.params.toList.map Param.arg
          assigned := (f.body.toList.map bodyAssigns).flatten
          boundBefore := directBinds f.body.toList
          yfForbidden := (f.body.toList.map yfNames).flatten
          walrusForbidden := f.params.toList.map Param.arg
            ++ (f.body.toList.map stmtNamesXW).flatten }
      let (body', st') := (lowerStmts ctx f.body).run st
      (acc.push { f with body := body' }, st')
  let topCtx : LowerCtx :=
    { outer, params := [], assigned := []
      walrusForbidden := (topLevel.toList.map stmtNamesXW).flatten }
  let (topLevel', st'') := (lowerStmts topCtx topLevel).run step.2
  (step.1 ++ st''.2, topLevel')

mutual
  /-- pass 5 (docs/memory-model.md §search()'s first blockers): CHAINED
  assignment splits at ingestion when the FIRST target is a plain name —
  `t1 = t2 = … = v` ⇢ `t1 = v; t2 = t1; …` — CPython's DUP_TOP
  compilation with the duplicated top read back from `t1` (a frame-local
  name store followed by a name read returns exactly the stored value,
  pure and unobservable — `x = x.y = v` reads the NEW `x` for the
  receiver, as CPython does — and each later target's subexpressions
  still evaluate after the earlier stores, CPython's order). Runs FIRST
  among the lowering passes, so every later census sees plain
  single-target assigns riding the existing discipline. A chain whose
  first target is NOT a name cannot be split without re-evaluating or
  naming the RHS: it stays un-split and hits the standing loud
  multi-target refusal in `execStmt`. -/
  private partial def splitChainStmt : Stmt → List Stmt
    | .assign tgts v sp =>
      (match tgts.toList with
       | t1 :: t2 :: rest =>
         (match t1 with
          | .name id nsp =>
            .assign #[t1] v sp ::
              (t2 :: rest).map (fun t => .assign #[t] (.name id nsp) sp)
          | _ => [.assign tgts v sp])
       | _ => [.assign tgts v sp])
    | .whileLoop t b o sp =>
        [.whileLoop t (splitChainStmts b) (splitChainStmts o) sp]
    | .forStmt t it b o sp =>
        [.forStmt t it (splitChainStmts b) (splitChainStmts o) sp]
    | .ifStmt t b o sp =>
        [.ifStmt t (splitChainStmts b) (splitChainStmts o) sp]
    | .tryStmt b en h tu sp =>
        [.tryStmt (splitChainStmts b) en (splitChainStmts h) tu sp]
    | .defStmt n p ao lo hg ig body cap sp =>
        [.defStmt n p ao lo hg ig (splitChainStmts body) cap sp]
    | s => [s]

  /-- Elementwise `splitChainStmt`, splicing the splits in place. -/
  private partial def splitChainStmts (ss : Array Stmt) : Array Stmt :=
    ((ss.toList.map splitChainStmt).flatten).toArray
end

/-- Parse the `module` payload, splitting top-level `FunctionDef`s into
`Module.functions`, `ClassDef`s into `Module.classes` (methods flattened
into `functions` under qualified names, in source order), and everything
else into `Module.topLevel` (source order preserved within each); then
run the namedtuple recognition pass (above) to fill `Module.namedtuples`. -/
def parseModule (j : Json) : Except String Module :=
  withCtx "module" do
    let kind ← (← getField j "kind").getStr?
    unless kind == "Module" do
      throw s!"expected kind \"Module\", got {kind.quote}"
    let body ← (← getField j "body").getArr?
    let mut functions : Array FunctionDefn := #[]
    let mut topLevel : Array Stmt := #[]
    let mut classes : Array ClassDefn := #[]
    for stmtJson in body do
      let k ← (← getField stmtJson "kind").getStr?
      if k == "FunctionDef" then
        functions := functions.push (← parseFunctionDefn stmtJson)
      else if k == "ClassDef" then
        let (c, fns) ← parseClassDefn stmtJson
        classes := classes.push c
        functions := functions ++ fns
      else
        topLevel := topLevel.push (← parseStmt stmtJson)
    -- pass 5: split chained assignments FIRST, so the namedtuple
    -- recognition, the exception census, and the genexp lowering all
    -- see plain single-target assigns (docs/memory-model.md §search()'s
    -- first blockers).
    functions := functions.map fun f => { f with body := splitChainStmts f.body }
    topLevel := splitChainStmts topLevel
    let (topLevel', namedtuples, classes') :=
      recognizeNamedtuples functions classes topLevel
    -- the exceptions-tier census (docs/memory-model.md §exceptions,
    -- as-built): an `exception_base` candidate keeps `isExc` only when
    -- `Exception` is provably the builtin — every top-level statement
    -- bind-analyzable, `Exception` bound nowhere (no top-level bind, no
    -- def/class/namedtuple of that name), and no `global` anywhere that
    -- could rebind it at call time. ANY failure demotes every candidate
    -- to the ordinary loud state (isExc := false, ok := false).
    let excOk :=
      (match topLevel'.toList.mapM stmtBinds with
       | some bindss => !(bindss.flatten.contains "Exception")
       | Option.none => false)
      && functions.toList.all (fun f => f.name != "Exception" && !f.hasGlobal)
      && classes'.toList.all (fun c => c.name != "Exception" && !c.hasGlobal)
      && namedtuples.toList.all (fun nt => nt.name != "Exception")
    let classes' :=
      if excOk then classes'
      else classes'.map fun c =>
        if c.isExc then
          { c with isExc := false, ok := false, creationPure := false } else c
    -- H4: lower generator EXPRESSIONS last, so the capture test sees the
    -- final module-level binding set (the namedtuple pass turns
    -- recognized assigns into `pass`, but their bound names stay outer
    -- names — `Move`/`Entry` resolve as constructors).
    let outer :=
      functions.toList.map FunctionDefn.name
        ++ classes'.toList.map ClassDefn.name
        ++ namedtuples.toList.map NamedTupleDefn.name
        ++ (topLevel.toList.map (fun st => (stmtBinds st).getD [])).flatten
    let (functions', topLevel'') := lowerGenExps outer functions topLevel'
    return { functions := functions', topLevel := topLevel'',
             classes := classes', namedtuples }

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
