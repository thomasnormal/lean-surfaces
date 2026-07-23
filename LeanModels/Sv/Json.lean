import Lean
import LeanModels.Sv.Ast

/-!
# SV envelope JSON ingestion (`LeanModels.Sv`)

Parses the SV M0 envelope (`docs/sv-design-m0.md` "Frontend": schema
`"sv-0.1"`, language `"systemverilog"`) from `Lean.Json` into the types of
`Ast.lean`. All parsers are pure `Except String _`; malformed input yields a
descriptive `.error`, never a panic.

**Vocabulary note.** This file was written against the design contract while
`docs/sv-envelope-schema.md` was still being authored, so the parser accepts
a small set of alternate spellings per node kind / field (canonical name
listed first in each match). Out-of-tier constructs must arrive as
`{"kind": "Unsupported", "sv_kind": …, "text": …}` (extractor contract);
a `kind` outside the vocabulary is therefore a schema mismatch and produces
a descriptive **error** (loud), not an `unsupported` node.

Canonical vocabulary assumed (kind: fields):
* `Literal`: `width` (Nat), `value` (binary digit string MSB-first with
  `0 1 x z _`, extended/truncated to `width` per §5.7.1 — or a JSON Nat)
* `Ident`: `name`
* `Unary`: `op` (`"~" "!" "-"`), `arg`
* `Binary`: `op` (`"+" "-" "&" "|" "^" "==" "!=" "<" "<=" ">" ">="`),
  `left`, `right`
* `Ternary`: `cond`, `then_expr`, `else_expr`
* `Concat`: `parts` (source order, first = most significant)
* `BlockingAssign` / `NonblockingAssign`: `target` (String), `value`
* `If`: `cond`, `then_branch`, `else_branch` (null/absent = no else)
* `Block`: `body`
* `AlwaysFF` / `Always`: `clock` (String), `body`; `AlwaysComb`: `body`;
  `Assign`: `target`, `value`
* `Decl`: `name`, `width`, `is_input`, `is_output` (Bool, default false),
  `init` (literal value at decl width, null/absent = none)
* design payload: `kind` `"Module"`, `name`, `decls`, `processes`
* `Unsupported` (expr/stmt/process): `sv_kind`, `text`

Entry points: `loadDesign : Lean.Json → Except String Design` (envelope in,
design out), plus `parseEnvelope` / `parseEnvelopeString` /
`loadDesignString` and the payload-level `parseDesign`.
-/

namespace LeanModels.Sv

open Lean (Json)

/-- The full envelope (one per source file). `frontend` and `lean_blocks`
(reserved, `[]` in M0) are accepted but not retained. -/
structure Envelope where
  schemaVersion : String
  language : String
  sourceFile : String
  sourceSha256 : String
  design : Design
deriving Repr, BEq, Inhabited

/-- Prefix an error message with context. -/
private def withCtx (c : String) : Except String α → Except String α
  | .ok a => .ok a
  | .error e => .error s!"{c}: {e}"

/-- Required object field, trying alternate spellings (canonical first). -/
private def getField (j : Json) (names : List String) : Except String Json :=
  match names.findSome? fun n => (j.getObjVal? n).toOption with
  | some v => .ok v
  | none => .error s!"missing field '{names.head?.getD "?"}' (accepted spellings: {names})"

/-- Optional field: absent or `null` ↦ `none`. -/
private def getOptField (j : Json) (names : List String) : Option Json :=
  match names.findSome? fun n => (j.getObjVal? n).toOption with
  | some .null => none
  | other => other

private def getStrField (j : Json) (names : List String) : Except String String := do
  withCtx s!"field '{names.head?.getD "?"}'" ((← getField j names).getStr?)

private def getNatField (j : Json) (names : List String) : Except String Nat := do
  withCtx s!"field '{names.head?.getD "?"}'" ((← getField j names).getNat?)

/-- Bool field defaulting to `false` when absent/null. -/
private def getBoolFieldD (j : Json) (names : List String) : Except String Bool :=
  match getOptField j names with
  | none => .ok false
  | some v => withCtx s!"field '{names.head?.getD "?"}'" v.getBool?

/-- The node `kind` discriminator. -/
private def getKind (j : Json) : Except String String :=
  withCtx "node" (getStrField j ["kind"])

/-- Parse an `Unsupported` payload (shared by expr/stmt/process). `text` is
optional (defaults to `""`); `sv_kind` is required. -/
private def parseUnsupportedFields (j : Json) : Except String (String × String) := do
  let svKind ← getStrField j ["sv_kind", "svKind"]
  let text := (getOptField j ["text"]).bind (·.getStr?.toOption) |>.getD ""
  return (svKind, text)

/-- A 4-state literal value at a known width: a binary digit string
(MSB-first, `0 1 x X z Z _`; extended/truncated to `width` per §5.7.1 via
`LVec.ofBinLit?`) or a JSON Nat (`LVec.ofNat width`). -/
def parseLVecValue (width : Nat) (j : Json) : Except String LVec :=
  match j with
  | .str s =>
      match LVec.ofBinLit? width s with
      | some v => .ok v
      | none => .error s!"invalid 4-state digit string {s.quote} (want 0 1 x z _, MSB-first)"
  | _ =>
      match j.getNat? with
      | .ok n => .ok (LVec.ofNat width n)
      | .error _ => .error s!"literal value must be a digit string or a Nat, got {j.compress}"

/-- M0 unary operator names (canonical: the SV symbol; slang enum-style
spellings accepted). -/
def parseUnaryOpName : String → Except String UnaryOp
  | "~" | "BitwiseNot" => .ok .bnot
  | "!" | "LogicalNot" => .ok .lnot
  | "-" | "Minus" | "UnaryMinus" | "Neg" => .ok .neg
  | s => .error s!"unknown unary op {s.quote}"

/-- M0 binary operator names (canonical: the SV symbol; slang enum-style
spellings accepted). `===`/`!==` are deliberately absent — not in the M0
expression tier; the extractor emits them as `Unsupported`. -/
def parseBinOpName : String → Except String BinOp
  | "+" | "Add" => .ok .add
  | "-" | "Subtract" | "Sub" => .ok .sub
  | "&" | "BinaryAnd" | "And" => .ok .and
  | "|" | "BinaryOr" | "Or" => .ok .or
  | "^" | "BinaryXor" | "Xor" => .ok .xor
  | "==" | "Equality" | "Eq" => .ok .eq
  | "!=" | "Inequality" | "Ne" => .ok .ne
  | "<" | "LessThan" | "Lt" => .ok .lt
  | "<=" | "LessThanEqual" | "Le" => .ok .le
  | ">" | "GreaterThan" | "Gt" => .ok .gt
  | ">=" | "GreaterThanEqual" | "Ge" => .ok .ge
  | s => .error s!"unknown binary op {s.quote}"

/-- Parse an expression node. `partial` because the recursion is over the
`Json` tree (through object/array lookups), not structural; ingestion is
executable code only — no theorems are proved about the parser itself. -/
partial def parseExpr (j : Json) : Except String Expr := do
  let kind ← getKind j
  withCtx kind do
    match kind with
    | "Literal" | "Lit" =>
        let width ← getNatField j ["width"]
        return .lit (← parseLVecValue width (← getField j ["value", "bits"]))
    | "Ident" | "Identifier" | "Name" =>
        return .ident (← getStrField j ["name", "id"])
    | "Unary" | "UnaryOp" =>
        let op ← parseUnaryOpName (← getStrField j ["op"])
        return .unary op (← parseExpr (← getField j ["arg", "operand"]))
    | "Binary" | "BinaryOp" | "BinOp" =>
        let op ← parseBinOpName (← getStrField j ["op"])
        return .binary op (← parseExpr (← getField j ["left"]))
          (← parseExpr (← getField j ["right"]))
    | "Ternary" | "Conditional" =>
        return .ternary (← parseExpr (← getField j ["cond", "condition"]))
          (← parseExpr (← getField j ["then_expr", "then", "true_expr"]))
          (← parseExpr (← getField j ["else_expr", "else", "false_expr"]))
    | "Concat" | "Concatenation" =>
        let parts ← (← (← getField j ["parts", "elements", "operands"]).getArr?).mapM parseExpr
        return .concat parts
    | "Unsupported" =>
        let (svKind, text) ← parseUnsupportedFields j
        return .unsupported svKind text
    | other => throw s!"unknown expression kind {other.quote} (schema mismatch — see docs/sv-envelope-schema.md)"

/-- Parse a statement node (see `parseExpr` for why `partial`). -/
partial def parseStmt (j : Json) : Except String Stmt := do
  let kind ← getKind j
  withCtx kind do
    match kind with
    | "BlockingAssign" =>
        return .blockingAssign (← getStrField j ["target", "lhs"])
          (← parseExpr (← getField j ["value", "rhs"]))
    | "NonblockingAssign" | "NbaAssign" | "NonBlockingAssign" =>
        return .nbaAssign (← getStrField j ["target", "lhs"])
          (← parseExpr (← getField j ["value", "rhs"]))
    | "If" | "IfStmt" =>
        let cond ← parseExpr (← getField j ["cond", "condition"])
        let thenBranch ← parseStmt (← getField j ["then_branch", "then", "then_stmt"])
        let elseBranch ← match getOptField j ["else_branch", "else", "else_stmt"] with
          | none => pure none
          | some je => pure (some (← parseStmt je))
        return .ifStmt cond thenBranch elseBranch
    | "Block" | "Begin" | "SeqBlock" =>
        return .block (← (← (← getField j ["body", "stmts", "statements"]).getArr?).mapM parseStmt)
    | "Unsupported" =>
        let (svKind, text) ← parseUnsupportedFields j
        return .unsupported svKind text
    | other => throw s!"unknown statement kind {other.quote} (schema mismatch — see docs/sv-envelope-schema.md)"

/-- Parse a process node. -/
def parseProcess (j : Json) : Except String Process := do
  let kind ← getKind j
  withCtx kind do
    match kind with
    | "AlwaysFF" | "always_ff" =>
        return .alwaysFF (← getStrField j ["clock", "clk"]) (← parseStmt (← getField j ["body"]))
    | "Always" | "AlwaysPlain" | "always" =>
        return .alwaysPlain (← getStrField j ["clock", "clk"]) (← parseStmt (← getField j ["body"]))
    | "AlwaysComb" | "always_comb" =>
        return .alwaysComb (← parseStmt (← getField j ["body"]))
    | "Assign" | "ContinuousAssign" | "assign" =>
        return .assign (← getStrField j ["target", "lhs"])
          (← parseExpr (← getField j ["value", "rhs"]))
    | "Unsupported" =>
        let (svKind, text) ← parseUnsupportedFields j
        return .unsupported svKind text
    | other => throw s!"unknown process kind {other.quote} (schema mismatch — see docs/sv-envelope-schema.md)"

/-- Parse a declaration. `init`, when present, is parsed at the declared
width (same value encoding as `Literal`). -/
def parseDecl (j : Json) : Except String Decl :=
  withCtx "Decl" do
    let name ← getStrField j ["name"]
    withCtx name.quote do
      let width ← getNatField j ["width"]
      let isInput ← getBoolFieldD j ["is_input", "isInput"]
      let isOutput ← getBoolFieldD j ["is_output", "isOutput"]
      let init ← match getOptField j ["init"] with
        | none => pure none
        | some ji => pure (some (← withCtx "init" (parseLVecValue width ji)))
      return { name, width, isInput, isOutput, init }

/-- Parse the `design` payload (a single elaborated M0 module). A `kind`
field, if present, must be `"Module"` or `"Design"`. -/
def parseDesign (j : Json) : Except String Design :=
  withCtx "design" do
    match getOptField j ["kind"] with
    | none => pure ()
    | some k =>
        let k ← k.getStr?
        unless k == "Module" || k == "Design" do
          throw s!"expected kind \"Module\", got {k.quote}"
    let name ← getStrField j ["name"]
    let decls ← (← (← getField j ["decls", "declarations"]).getArr?).mapM parseDecl
    let processes ← (← (← getField j ["processes"]).getArr?).mapM parseProcess
    return { name, decls, processes }

/-- Parse a full envelope document. Validates `schema_version = "sv-0.1"`
and `language = "systemverilog"` loudly (wrong-lane files must not slip
through); `frontend`/`lean_blocks` accepted, not retained. -/
def parseEnvelope (j : Json) : Except String Envelope :=
  withCtx "envelope" do
    let schemaVersion ← getStrField j ["schema_version"]
    unless schemaVersion == "sv-0.1" do
      throw s!"unsupported schema_version {schemaVersion.quote} (want \"sv-0.1\")"
    let language ← getStrField j ["language"]
    unless language == "systemverilog" do
      throw s!"unsupported language {language.quote} (want \"systemverilog\")"
    return { schemaVersion, language
             sourceFile := ← getStrField j ["source_file"]
             sourceSha256 := ← getStrField j ["source_sha256"]
             design := ← parseDesign (← getField j ["design"]) }

/-- The main entry point: envelope JSON in, `Design` out. -/
def loadDesign (j : Json) : Except String Design :=
  (·.design) <$> parseEnvelope j

/-- Convenience: JSON text → `Envelope` (composes `Lean.Json.parse`). -/
def parseEnvelopeString (s : String) : Except String Envelope :=
  Json.parse s >>= parseEnvelope

/-- Convenience: JSON text → `Design`. -/
def loadDesignString (s : String) : Except String Design :=
  (·.design) <$> parseEnvelopeString s

/-! ## Inline tests — hand-written envelopes only

(Deliberately NOT reading
`Examples/system-verilog/<design>/*.sv.json` from disk: those are
generated by a concurrently-built extractor; the harness phase diffs
against them.) -/

/-- Hand-written envelope for `Examples/system-verilog/counter/counter.sv` in the canonical
vocabulary (sha256 is a placeholder; the parser does not validate it). -/
private def counterEnvelopeText : String := r#"{
  "schema_version": "sv-0.1",
  "language": "systemverilog",
  "frontend": {"name": "pyslang", "version": "11.0.0"},
  "source_file": "Examples/system-verilog/counter/counter.sv",
  "source_sha256": "0000000000000000000000000000000000000000000000000000000000000000",
  "design": {
    "kind": "Module",
    "name": "counter",
    "decls": [
      {"kind": "Decl", "name": "clk", "width": 1, "is_input": true, "is_output": false, "init": null},
      {"kind": "Decl", "name": "rst", "width": 1, "is_input": true, "is_output": false, "init": null},
      {"kind": "Decl", "name": "count", "width": 8, "is_input": false, "is_output": true, "init": null}
    ],
    "processes": [
      {"kind": "AlwaysFF", "clock": "clk",
       "body": {"kind": "If",
                "cond": {"kind": "Ident", "name": "rst"},
                "then_branch": {"kind": "NonblockingAssign", "target": "count",
                                "value": {"kind": "Literal", "width": 8, "value": "0"}},
                "else_branch": {"kind": "NonblockingAssign", "target": "count",
                                "value": {"kind": "Binary", "op": "+",
                                          "left": {"kind": "Ident", "name": "count"},
                                          "right": {"kind": "Literal", "width": 8, "value": "00000001"}}}}}
    ]
  },
  "lean_blocks": []
}"#

/-- What the counter envelope must parse to (note `"0"` at width 8 →
`8'b00000000` by 0-extension). -/
private def counterExpected : Design :=
  { name := "counter"
    decls := #[
      { name := "clk", width := 1, isInput := true },
      { name := "rst", width := 1, isInput := true },
      { name := "count", width := 8, isOutput := true }]
    processes := #[
      .alwaysFF "clk" (.ifStmt (.ident "rst")
        (.nbaAssign "count" (.lit (.ofNat 8 0)))
        (some (.nbaAssign "count"
          (.binary .add (.ident "count") (.lit (.ofNat 8 1))))))] }

#guard (loadDesignString counterEnvelopeText).toOption == some counterExpected
#guard ((parseEnvelopeString counterEnvelopeText).map (·.sourceFile)).toOption
        == some "Examples/system-verilog/counter/counter.sv"

/-- Second envelope: `race_blk`-style — initializers, plain `always`,
blocking assigns, plus an `Unsupported` process (an `initial` block). -/
private def raceEnvelopeText : String := r#"{
  "schema_version": "sv-0.1",
  "language": "systemverilog",
  "frontend": {"name": "pyslang", "version": "11.0.0"},
  "source_file": "Examples/system-verilog/race_blk/race_blk.sv",
  "source_sha256": "0000000000000000000000000000000000000000000000000000000000000000",
  "design": {
    "kind": "Module",
    "name": "race_blk",
    "decls": [
      {"kind": "Decl", "name": "clk", "width": 1, "is_input": true, "is_output": false, "init": null},
      {"kind": "Decl", "name": "a", "width": 8, "is_input": false, "is_output": false, "init": "00000001"},
      {"kind": "Decl", "name": "b", "width": 8, "is_input": false, "is_output": false, "init": 2}
    ],
    "processes": [
      {"kind": "Always", "clock": "clk",
       "body": {"kind": "BlockingAssign", "target": "a", "value": {"kind": "Ident", "name": "b"}}},
      {"kind": "Always", "clock": "clk",
       "body": {"kind": "BlockingAssign", "target": "b", "value": {"kind": "Ident", "name": "a"}}},
      {"kind": "Unsupported", "sv_kind": "ProceduralBlockSymbol:Initial", "text": "initial begin #10; end"}
    ]
  },
  "lean_blocks": []
}"#

private def raceExpected : Design :=
  { name := "race_blk"
    decls := #[
      { name := "clk", width := 1, isInput := true },
      { name := "a", width := 8, init := some (.ofNat 8 1) },
      { name := "b", width := 8, init := some (.ofNat 8 2) }]
    processes := #[
      .alwaysPlain "clk" (.blockingAssign "a" (.ident "b")),
      .alwaysPlain "clk" (.blockingAssign "b" (.ident "a")),
      .unsupported "ProceduralBlockSymbol:Initial" "initial begin #10; end"] }

#guard (loadDesignString raceEnvelopeText).toOption == some raceExpected
#guard ((loadDesignString raceEnvelopeText).map Design.hasUnsupported).toOption == some true

-- Error paths stay loud and descriptive.
#guard (parseExpr (Json.mkObj [("kind", "PowerExpression")])).isOk == false
#guard (loadDesignString "{\"schema_version\": \"0.1\"}").isOk == false  -- Python-lane version
#guard (Json.parse "{\"kind\": \"Ident\"}" >>= parseExpr).isOk == false  -- missing name
-- 4-state literal digits (x/z) survive ingestion.
#guard (parseExpr (Json.mkObj [("kind", "Literal"), ("width", (2 : Nat)), ("value", "1x")])).toOption
        == some (.lit (.lit "1x"))

end LeanModels.Sv
