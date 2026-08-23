import Lean
import LeanModels.Sv.Param
import LeanModels.Sv.Param2

/-!
# SV symbolic-envelope ingestion — schema sv-0.2 (`LeanModels.Sv`)

Parses the phase-1 **symbolic** envelopes (`docs/sv-envelope-schema.md`,
"Symbolic mode — schema sv-0.2": `--top` extraction over the CV32E40P RTL)
into the parametric design AST of `Param.lean`, and provides the

```
load_design_sv2 ff_one from "Examples/system-verilog/ff_one/cv32e40p_ff_one.sv.json"
```

command elaborating an envelope to a **parametric value**. All parsers are
pure `Except String _` (loud on malformed input, never a panic); the
proof-relevant semantics (`PDesign.instantiate` and its lemmas) lives
entirely in `Param.lean`, which imports no `Lean.Json` — this file is
executable ingestion glue only.

## The parameter-binder encoding (the normative decision)

`load_design_sv2 name from "x.json"` defines **two** constants:

* `name.pdesign : PDesign` — the parsed envelope as a literal first-order
  term (via `ToExpr`, the Python lane's `load_program` discipline), so
  proofs can unfold it;
* `name : (P₁ : Nat) → … → (Pₙ : Nat) → Design` — the design family:
  one **explicit `Nat` binder per SV `parameter`, named exactly as in
  source, in declaration order**, with body
  `PDesign.instantiateD name.pdesign [Int.ofNat P₁, …, Int.ofNat Pₙ]`.

Why `Nat` and not `Int`: SV value parameters are 32-bit signed ints, and
`PDesign.instantiate : PDesign → List Int → …` keeps that honest domain —
but every CV32E40P parameter is a width/count/flag, the spec gallery
(`docs/cv32e40p-spec-surface.md`) quantifies `∀ LEN : Nat`, and `Nat`
binders keep `Decl.width : Nat` arithmetic cast-free in ∀-parameter
theorems. The `Int` core remains reachable (`name.pdesign.instantiate
[-1, …]` is expressible and loud), so the surface choice narrows nothing;
it only picks the theorem-friendly binder type. Localparams are **not**
binders (they are computed by `instantiate`, in declaration order).

## Load-time differential test (refusal, not trust)

The envelope's `resolved`-family fields are slang's own
defaults-elaboration metadata. At elaboration time the command replays our
elaboration at the defaults (`PDesign.crossCheck`) and **refuses the
envelope** on any mismatch (parameter defaults, localparams, declared
widths, top-level generate counts) — the ingestion-time differential test
against the frontend, in the lane's diff-before-theorems discipline.

Recorded limitations (loud, never silent): a parameter whose default
references a localparam (interleaving is lost by the params/localParams
split — no CV32E40P file does this) and a parameter without a default
both fail `crossCheck` and refuse the load; `SysCall` nodes with arity ≠ 1
parse to loud `unsupported` expressions.
-/

namespace LeanModels.Sv

open Lean (Json ToExpr toExpr)

/-! ## `ToExpr` instances (elaboration-time quoting for `load_design_sv2`) -/

deriving instance Lean.ToExpr for Logic
deriving instance Lean.ToExpr for LVec
deriving instance Lean.ToExpr for UnaryOp
deriving instance Lean.ToExpr for BinOp
deriving instance Lean.ToExpr for SymBinOp
deriving instance Lean.ToExpr for SymUnaryOp
deriving instance Lean.ToExpr for SysFn
deriving instance Lean.ToExpr for RedOp
deriving instance Lean.ToExpr for CaseCheck
deriving instance Lean.ToExpr for PExpr
deriving instance Lean.ToExpr for PLhs
deriving instance Lean.ToExpr for PDim
deriving instance Lean.ToExpr for PType
deriving instance Lean.ToExpr for PParam
deriving instance Lean.ToExpr for PLocalParam
deriving instance Lean.ToExpr for EnumVal
deriving instance Lean.ToExpr for PEnumMember
deriving instance Lean.ToExpr for PEnumType
deriving instance Lean.ToExpr for PDecl
deriving instance Lean.ToExpr for PStmt
deriving instance Lean.ToExpr for PProcess
deriving instance Lean.ToExpr for GenItem
deriving instance Lean.ToExpr for PDesign

/-! ## JSON field helpers (strict sv-0.2 spellings — the schema is
normative and the extractor deterministic; no alternate spellings) -/

private def withCtx (c : String) : Except String α → Except String α
  | .ok a => .ok a
  | .error e => .error s!"{c}: {e}"

private def getField (j : Json) (name : String) : Except String Json :=
  match (j.getObjVal? name).toOption with
  | some v => .ok v
  | none => .error s!"missing field '{name}'"

/-- Optional field: absent or `null` ↦ `none`. -/
private def getOptField (j : Json) (name : String) : Option Json :=
  match (j.getObjVal? name).toOption with
  | some .null => none
  | other => other

private def getStrField (j : Json) (name : String) : Except String String := do
  withCtx s!"field '{name}'" ((← getField j name).getStr?)

private def getNatField (j : Json) (name : String) : Except String Nat := do
  withCtx s!"field '{name}'" ((← getField j name).getNat?)

private def getIntField (j : Json) (name : String) : Except String Int := do
  withCtx s!"field '{name}'" ((← getField j name).getInt?)

/-- Optional string field. -/
private def getOptStr (j : Json) (name : String) : Option String :=
  (getOptField j name).bind (·.getStr?.toOption)

/-- Optional metadata field (`resolved`-family) — never load-bearing, so
an unparseable value degrades to `none`, silently by design. -/
private def getOptNat (j : Json) (name : String) : Option Nat :=
  (getOptField j name).bind (·.getNat?.toOption)

private def getOptInt (j : Json) (name : String) : Option Int :=
  (getOptField j name).bind (·.getInt?.toOption)

private def getKind (j : Json) : Except String String :=
  withCtx "node" (getStrField j "kind")

private def parseUnsupportedFields (j : Json) : Except String (String × String) := do
  let svKind ← getStrField j "sv_kind"
  let text := (getOptField j "text").bind (·.getStr?.toOption) |>.getD ""
  return (svKind, text)

/-! ## Operator tables -/

/-- sv-0.2 binary operator spellings: the M0 set, the symbolic-position
extras, signed order comparisons (`s<` …), and the self-check-tier extras. -/
def parseSymBinOp : String → Except String SymBinOp
  | "+" => .ok (.m0 .add) | "-" => .ok (.m0 .sub)
  | "&" => .ok (.m0 .and) | "|" => .ok (.m0 .or) | "^" => .ok (.m0 .xor)
  | "==" => .ok (.m0 .eq) | "!=" => .ok (.m0 .ne)
  | "<" => .ok (.m0 .lt) | "<=" => .ok (.m0 .le)
  | ">" => .ok (.m0 .gt) | ">=" => .ok (.m0 .ge)
  | "*" => .ok .mul | "/" => .ok .div | "%" => .ok .mod | "**" => .ok .pow
  | "<<" => .ok .shl | ">>" => .ok .shr | "<<<" => .ok .ashl | ">>>" => .ok .ashr
  | "s<" => .ok .slt | "s<=" => .ok .sle | "s>" => .ok .sgt | "s>=" => .ok .sge
  | "===" => .ok .ceq | "!==" => .ok .cne | "&&" => .ok .land | "||" => .ok .lor
  | s => .error s!"unknown binary op {s.quote}"

/-- sv-0.2 unary operator spellings (`++`/`--` are legal only in
`GenerateFor.step` position — `instantiate` enforces that, not the parser). -/
def parseSymUnaryOp : String → Except String SymUnaryOp
  | "~" => .ok (.m0 .bnot) | "!" => .ok (.m0 .lnot) | "-" => .ok (.m0 .neg)
  | "+" => .ok .plus | "++" => .ok .inc | "--" => .ok .dec
  | s => .error s!"unknown unary op {s.quote}"

def parseSysFn : String → Except String SysFn
  | "$clog2" => .ok .clog2 | "$bits" => .ok .bits
  | "$high" => .ok .high | "$size" => .ok .size
  | s => .error s!"unknown system function {s.quote}"

/-- Reduction-operator spellings of the semantic tier. -/
def parseRedOp : String → Except String RedOp
  | "|" => .ok .or | "&" => .ok .and | "^" => .ok .xor
  | "~|" => .ok .nor | "~&" => .ok .nand | "~^" => .ok .xnor
  | s => .error s!"unknown reduction op {s.quote}"

/-- `case` check-qualifier spellings. -/
def parseCaseCheck : String → Except String CaseCheck
  | "none" => .ok .none | "unique" => .ok .unique
  | "unique0" => .ok .unique0 | "priority" => .ok .priority
  | s => .error s!"unknown case check {s.quote}"

private def parseLogicBit : String → Except String Logic
  | "0" => .ok .l0 | "1" => .ok .l1 | "x" => .ok .lx | "z" => .ok .lz
  | s => .error s!"unknown fill bit {s.quote}"

/-! ## Expressions -/

/-- Parse an sv-0.2 expression node. `width` fields on expression nodes are
default-elaborated metadata and are **ignored** (the binding symbolic
widths live on declarations; `Param.lean` computes its own). `partial`
because the recursion is over the `Json` tree — ingestion is executable
code only, no theorems mention the parser. -/
partial def parsePExpr (j : Json) : Except String PExpr := do
  let kind ← getKind j
  withCtx kind do
    match kind with
    | "Literal" =>
        let width ← getNatField j "width"
        let bits ← getStrField j "bits"
        match LVec.ofBinLit? width bits with
        | some v => return .lit v
        | none => throw s!"invalid 4-state digit string {bits.quote}"
    | "Ident" => return .ident (← getStrField j "name")
    | "ParamRef" => return .paramRef (← getStrField j "name") (getOptStr j "from_package")
    | "GenvarRef" => return .genvarRef (← getStrField j "name")
    | "EnumRef" =>
        return .enumRef (← getStrField j "type") (← getStrField j "member")
          (getOptStr j "from_package")
    | "Int" => return .int (← getIntField j "value")
    | "Fill" => return .fill (← parseLogicBit (← getStrField j "bit"))
    | "Unary" =>
        return .unary (← parseSymUnaryOp (← getStrField j "op"))
          (← parsePExpr (← getField j "operand"))
    | "Binary" =>
        return .binary (← parseSymBinOp (← getStrField j "op"))
          (← parsePExpr (← getField j "left")) (← parsePExpr (← getField j "right"))
    | "Ternary" =>
        return .ternary (← parsePExpr (← getField j "cond"))
          (← parsePExpr (← getField j "then")) (← parsePExpr (← getField j "else"))
    | "Concat" =>
        return .concat (← (← (← getField j "parts").getArr?).toList.mapM parsePExpr)
    | "Resize" =>
        return .resize (← getNatField j "width") (← parsePExpr (← getField j "operand"))
    | "Squash2" =>
        -- 4-state → 2-state squash (2-state parameter/localparam types,
        -- e.g. `parameter int unsigned`): value-preserving in the constant
        -- tier, loud in value positions (`instExpr*`'s Squash2 arm).
        return .squash2 (← getNatField j "width") (← parsePExpr (← getField j "operand"))
    | "BitSel" =>
        return .bitSel (← parsePExpr (← getField j "value"))
          (← parsePExpr (← getField j "index"))
    | "PartSel" =>
        return .partSel (← parsePExpr (← getField j "value"))
          (← parsePExpr (← getField j "msb")) (← parsePExpr (← getField j "lsb"))
    | "Repl" =>
        return .repl (← parsePExpr (← getField j "count"))
          (← parsePExpr (← getField j "operand"))
    | "Reduce" =>
        return .reduce (← parseRedOp (← getStrField j "op"))
          (← parsePExpr (← getField j "operand"))
    | "Cast" =>
        let signed ← match getOptField j "signed" with
          | some (Json.bool b) => pure b
          | _ => throw "field 'signed' is not a bool"
        return .cast signed (← parsePExpr (← getField j "operand"))
    | "SysCall" =>
        let fn ← parseSysFn (← getStrField j "name")
        let args ← (← (← getField j "args").getArr?).toList.mapM parsePExpr
        match args with
        | [a] => return .sysCall fn a
        | _ => return .unsupported "SysCall:arity" s!"{fn.sym} with {args.length} args"
    | "Unsupported" =>
        let (svKind, text) ← parseUnsupportedFields j
        return .unsupported svKind text
    | other => throw s!"unknown expression kind {other.quote} (schema mismatch — see docs/sv-envelope-schema.md)"

/-! ## Types -/

private def parsePDim (j : Json) : Except String PDim := do
  return { msb := ← parsePExpr (← getField j "msb"), lsb := ← parsePExpr (← getField j "lsb") }

/-- A declared type: `PackedType` (symbolic bounds; `packed: null` =
unrecoverable — the `resolved` width survives as metadata) or `TypeRef`. -/
def parsePType (j : Json) : Except String PType := do
  let kind ← getKind j
  withCtx kind do
    match kind with
    | "PackedType" =>
        let resolved? := getOptNat j "resolved"
        match getOptField j "packed" with
        | none => return .unrecoverable resolved?
        | some dims =>
            return .packed (← (← dims.getArr?).toList.mapM parsePDim) resolved?
    | "TypeRef" =>
        return .typeRef (← getStrField j "name") (getOptStr j "from_package")
          (getOptNat j "resolved")
    | other => throw s!"unknown type kind {other.quote}"

/-! ## Statements and processes -/

/-- Assignment targets are whole-signal `Ident` nodes in this tier; anything
else degrades to a loud unsupported statement (extractor contract already
guarantees this — defensive here). -/
private def parseTarget (j : Json) : Except String (Except String String) := do
  match ← parsePExpr j with
  | .ident n => return .ok n
  | _ => return .error "AssignmentExpression:target"

/-- Semantic-tier assignment targets: whole signal, or one `BitSel`/
`PartSel` over an identifier base (the extractor's `_target_shape_ok`
contract). Anything else degrades to a loud unsupported statement. -/
private def parseTargetL (j : Json) : Except String (Except String PLhs) := do
  match ← parsePExpr j with
  | .ident n => return .ok (.ident n)
  | .bitSel (.ident n) idx => return .ok (.bitSel n idx)
  | .partSel (.ident n) msb lsb => return .ok (.partSel n msb lsb)
  | _ => return .error "AssignmentExpression:target"

partial def parsePStmt (j : Json) : Except String PStmt := do
  let kind ← getKind j
  withCtx kind do
    match kind with
    | "BlockingAssign" | "NonblockingAssign" =>
        let value ← parsePExpr (← getField j "value")
        match ← parseTargetL (← getField j "target") with
        | .error k => return .unsupported k "non-select assignment target"
        | .ok (.ident t) =>
            -- Ident targets keep the M0 constructors (old envelopes parse
            -- to identical PDesign values).
            return if kind == "BlockingAssign" then .blockingAssign t value
                   else .nbaAssign t value
        | .ok lhs =>
            return if kind == "BlockingAssign" then .blockingAssignL lhs value
                   else .nbaAssignL lhs value
    | "If" =>
        let cond ← parsePExpr (← getField j "cond")
        let thenB ← parsePStmt (← getField j "then")
        let elseB ← match getOptField j "else" with
          | none => pure none
          | some je => pure (some (← parsePStmt je))
        return .ifStmt cond thenB elseB
    | "Block" =>
        return .block (← (← (← getField j "stmts").getArr?).toList.mapM parsePStmt)
    | "Case" =>
        let check ← parseCaseCheck (← getStrField j "check")
        let inside ← match ← getStrField j "match" with
          | "normal" => pure false
          | "inside" => pure true
          | s => throw s!"unknown case match kind {s.quote}"
        let subject ← parsePExpr (← getField j "subject")
        let items ← (← (← getField j "items").getArr?).toList.mapM fun ij => do
          let pats ← (← (← getField ij "patterns").getArr?).toList.mapM parsePExpr
          let body ← parsePStmt (← getField ij "body")
          pure (pats, body)
        let dflt ← match getOptField j "default" with
          | none => pure none
          | some dj => pure (some (← parsePStmt dj))
        return .caseStmt subject items dflt inside check
    | "Empty" => return .block []
    | "Unsupported" =>
        let (svKind, text) ← parseUnsupportedFields j
        return .unsupported svKind text
    | other => throw s!"unknown statement kind {other.quote}"

def parsePProcess (j : Json) : Except String PProcess := do
  let kind ← getKind j
  withCtx kind do
    match kind with
    | "AlwaysPosedge" =>
        let style ← getStrField j "style"
        let clock ← getStrField j "clock"
        let body ← parsePStmt (← getField j "body")
        match getOptStr j "areset_n" with
        | some rn =>
            -- `@(posedge clock or negedge rn)` — the async active-low
            -- reset event list (T-reset); style is metadata here.
            return .alwaysFFR clock rn body
        | none =>
        match style with
        | "always_ff" => return .alwaysFF clock body
        | "always" => return .alwaysPlain clock body
        | s => throw s!"unknown AlwaysPosedge style {s.quote}"
    | "AlwaysComb" => return .alwaysComb (← parsePStmt (← getField j "body"))
    | "Assign" =>
        let value ← parsePExpr (← getField j "value")
        match ← parseTargetL (← getField j "target") with
        | .error k => return .unsupported k "non-select assign target"
        | .ok (.ident t) => return .assign t value
        | .ok lhs => return .assignL lhs value
    | "Unsupported" =>
        let (svKind, text) ← parseUnsupportedFields j
        return .unsupported svKind text
    | other => throw s!"unknown process kind {other.quote}"

/-! ## Generate items -/

/-- Parse a generate-region member. Process shapes become `GenItem.process`;
nested `GenerateFor`/`GenerateIf` stay structural; generate-local
declarations (`Var`/`Net` inside a generate body — per-instance scoping,
outside this slice) become loud unsupported items. -/
partial def parseGenItem (j : Json) : Except String GenItem := do
  let kind ← getKind j
  withCtx kind do
    match kind with
    | "GenerateFor" =>
        let label := getOptStr j "label"
        let genvar ← getStrField j "genvar"
        let init ← parsePExpr (← getField j "init")
        let bound ← parsePExpr (← getField j "bound")
        let step ← parsePExpr (← getField j "step")
        let rc? := getOptNat j "resolved_count"
        let body ← (← (← getField j "body").getArr?).toList.mapM parseGenItem
        return .genFor label genvar init bound step rc? body
    | "GenerateIf" =>
        let cond ← parsePExpr (← getField j "cond")
        let thenB ← (← (← getField j "then").getArr?).toList.mapM parseGenItem
        let elseB ← match getOptField j "else" with
          | none => pure []
          | some je => (← je.getArr?).toList.mapM parseGenItem
        return .genIf cond thenB elseB
    | "AlwaysPosedge" | "AlwaysComb" | "Assign" => return .process (← parsePProcess j)
    | "Var" | "Net" =>
        return .unsupported s!"GenerateDecl:{kind}"
          s!"generate-local declaration '{(getOptStr j "name").getD "?"}'"
    | "Unsupported" =>
        let (svKind, text) ← parseUnsupportedFields j
        return .unsupported svKind text
    | other => throw s!"unknown generate member kind {other.quote}"

/-! ## Module and envelope -/

/-- Parse a `Port`/`Var`/`Net` declaration (symbolic `width` type object). -/
def parsePDecl (j : Json) : Except String PDecl := do
  let kind ← getKind j
  withCtx kind do
    let name ← getStrField j "name"
    withCtx name.quote do
      let ty ← parsePType (← getField j "width")
      match kind with
      | "Port" =>
          match ← getStrField j "dir" with
          | "in" => return { name, type := ty, isInput := true }
          | "out" => return { name, type := ty, isOutput := true }
          | d => throw s!"unknown port dir {d.quote}"
      | "Var" | "Net" =>
          let init ← match getOptField j "init" with
            | none => pure none
            | some ji => pure (some (← withCtx "init" (parsePExpr ji)))
          return { name, type := ty, isNet := kind == "Net", init }
      | other => throw s!"unknown declaration kind {other.quote}"

/-- Parse the sv-0.2 `Module` payload into a `PDesign`. `Unsupported`
members of any list are routed to `PDesign.others` — instantiation turns
them into loud unsupported processes, so no declaration or member is ever
silently dropped. `imports` are name-resolution metadata (package-scoped
references arrive as `ParamRef`/`EnumRef` with `from_package`) and are not
retained. -/
def parseModule2 (j : Json) : Except String PDesign :=
  withCtx "module" do
    let name ← getStrField j "name"
    let mut params : List PParam := []
    let mut localParams : List PLocalParam := []
    let mut enums : List PEnumType := []
    let mut decls : List PDecl := []
    let mut processes : List PProcess := []
    let mut generates : List GenItem := []
    let mut others : List (String × String) := []
    for pj in (← (← getField j "params").getArr?) do
      match ← getKind pj with
      | "ParameterDecl" =>
          let pname ← getStrField pj "name"
          let default? ← match getOptField pj "default" with
            | none => pure none
            | some dj => pure (some (← withCtx s!"parameter '{pname}' default" (parsePExpr dj)))
          let type? ← match getOptField pj "type" with
            | none => pure none
            | some tj => pure (some (← withCtx s!"parameter '{pname}' type" (parsePType tj)))
          params := params ++ [{ name := pname, default?, resolved? := getOptInt pj "resolved", type? }]
      | "LocalParam" =>
          let pname ← getStrField pj "name"
          let expr ← withCtx s!"localparam '{pname}'" (parsePExpr (← getField pj "expr"))
          let type? ← match getOptField pj "type" with
            | none => pure none
            | some tj => pure (some (← withCtx s!"localparam '{pname}' type" (parsePType tj)))
          localParams := localParams ++ [{ name := pname, expr, resolved? := getOptInt pj "resolved", type? }]
      | "Unsupported" => others := others ++ [← parseUnsupportedFields pj]
      | other => throw s!"unknown parameter kind {other.quote}"
    for tj in (← (← getField j "types").getArr?) do
      match ← getKind tj with
      | "EnumType" =>
          let ename ← getStrField tj "name"
          let base ← withCtx s!"enum '{ename}' base" (parsePType (← getField tj "base_width"))
          let members ← (← (← getField tj "members").getArr?).toList.mapM fun mj => do
            let mname ← getStrField mj "name"
            let value ← match getOptInt mj "value" with
              | some v => pure (EnumVal.int v)
              | none => pure (EnumVal.bits ((← getField mj "value").getStr?.toOption.getD "?"))
            pure { name := mname, value : PEnumMember }
          enums := enums ++ [{ name := ename, pkg := getOptStr tj "from_package", base, members }]
      | "Unsupported" => others := others ++ [← parseUnsupportedFields tj]
      | other => throw s!"unknown type kind {other.quote}"
    for dj in (← (← getField j "ports").getArr?) ++ (← (← getField j "decls").getArr?) do
      match ← getKind dj with
      | "Unsupported" => others := others ++ [← parseUnsupportedFields dj]
      | _ => decls := decls ++ [← parsePDecl dj]
    for pj in (← (← getField j "processes").getArr?) do
      processes := processes ++ [← parsePProcess pj]
    for gj in (← (← getField j "generates").getArr?) do
      generates := generates ++ [← parseGenItem gj]
    for oj in (← (← getField j "others").getArr?) do
      match ← getKind oj with
      | "Unsupported" => others := others ++ [← parseUnsupportedFields oj]
      | other => throw s!"unknown module member kind {other.quote}"
    return { name, params, localParams, enums, decls, processes, generates, others }

/-- An sv-0.2 envelope: parametric design + provenance metadata. -/
structure Envelope2 where
  top : String
  /-- `(path, sha256)` per source file, CLI order. -/
  sourceFiles : List (String × String)
  packages : List String
  design : PDesign
deriving Repr, BEq, Inhabited

/-- Parse a full sv-0.2 envelope. Validates `schema_version = "sv-0.2"`,
`language = "systemverilog"`, `mode = "symbolic"`, and exactly one module,
loudly. -/
def parseEnvelope2 (j : Json) : Except String Envelope2 :=
  withCtx "envelope" do
    let sv ← getStrField j "schema_version"
    unless sv == "sv-0.2" do
      throw s!"unsupported schema_version {sv.quote} (want \"sv-0.2\"; single-file M0 envelopes are sv-0.1 → Json.lean)"
    let lang ← getStrField j "language"
    unless lang == "systemverilog" do
      throw s!"unsupported language {lang.quote}"
    let mode ← getStrField j "mode"
    unless mode == "symbolic" do
      throw s!"unsupported mode {mode.quote} (want \"symbolic\")"
    let top ← getStrField j "top"
    let sourceFiles ← (← (← getField j "source_files").getArr?).toList.mapM fun sj => do
      pure (← getStrField sj "path", ← getStrField sj "sha256")
    let packages ← (← (← getField j "packages").getArr?).toList.mapM (·.getStr?)
    let design ← getField j "design"
    let modules ← (← getField design "modules").getArr?
    match modules.toList with
    | [m] =>
        let pd ← parseModule2 m
        unless pd.name == top do
          throw s!"module name {pd.name.quote} ≠ top {top.quote}"
        return { top, sourceFiles, packages, design := pd }
    | ms => throw s!"expected exactly one module, got {ms.length}"

/-- JSON text → `Envelope2`. -/
def parseEnvelope2String (s : String) : Except String Envelope2 :=
  Json.parse s >>= parseEnvelope2

/-- JSON text → `PDesign`. -/
def loadPDesignString (s : String) : Except String PDesign :=
  (·.design) <$> parseEnvelope2String s

/-! ## `load_design_sv2` -/

open Lean Elab Command in
/--
`load_design_sv2 ff_one from "Examples/system-verilog/ff_one/cv32e40p_ff_one.sv.json"`
reads an **sv-0.2 symbolic envelope** at elaboration time and defines the
parametric design family (see the module docstring for the binder
encoding):

* `ff_one.pdesign : PDesign` — the envelope as a literal term;
* `ff_one : Nat → … → Nat → Design` — one named explicit binder per SV
  `parameter`, declaration order, body `PDesign.instantiateD`.

Before defining anything the command replays the defaults elaboration and
compares it against the envelope's `resolved` metadata
(`PDesign.crossCheck`); any mismatch **refuses the envelope** with the
full message list — the ingestion-time differential test against slang.
Missing files, malformed envelopes, and redeclarations are elaboration
errors, never silent. Paths resolve against the cwd (the package root
under `lake build`).
-/
elab "load_design_sv2 " name:ident " from " path:str : command => do
  let pathStr := path.getString
  let contents ←
    match ← (IO.FS.readFile ⟨pathStr⟩).toBaseIO with
    | .ok c => pure c
    | .error e =>
        throwErrorAt path
          "load_design_sv2: cannot read '{pathStr}': {toString e}\n(relative paths resolve against the current working directory — the package root under `lake build`; current cwd: '{toString (← IO.currentDir)}')"
  let envl ←
    match parseEnvelope2String contents with
    | .error e => throwErrorAt path "load_design_sv2: '{pathStr}' is not a valid sv-0.2 envelope: {e}"
    | .ok envl => pure envl
  let pd := envl.design
  match pd.crossCheckFull with
  | ([], 0) =>
      -- VACUOUS: the differential test ran and compared NOTHING.  Before
      -- this arm existed, `[]` meant both "everything agreed" and "there
      -- was nothing to agree about", and an envelope carrying no
      -- `resolved` metadata passed the gate without a single comparison.
      throwErrorAt path
        "load_design_sv2: '{pathStr}' REFUSED — VACUOUS cross-check: the envelope carries no `resolved` metadata on any parameter, localparam, declaration width or generate count, so the Lean-vs-slang differential compared NOTHING. An empty message list is not agreement when no comparison was made."
  | ([], _) => pure ()
  | (msgs, _) =>
      throwErrorAt path
        "load_design_sv2: '{pathStr}' REFUSED — our defaults elaboration disagrees with the envelope's `resolved` metadata (Lean vs slang differential):\n  {String.intercalate "\n  " msgs}"
  let funName := (← getCurrNamespace) ++ name.getId
  let pdName := funName ++ `pdesign
  let semName := funName ++ `sem
  for n in [funName, pdName, semName] do
    if (← getEnv).contains n then
      throwErrorAt name "load_design_sv2: '{n}' has already been declared"
  let paramNames := pd.params.map (·.name)
  liftCoreM do
    addAndCompile <| .defnDecl {
      name := pdName
      levelParams := []
      type := Lean.mkConst ``LeanModels.Sv.PDesign
      value := toExpr pd
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst pdName
    addDocStringCore pdName
      s!"Parametric design loaded by `load_design_sv2` from `{pathStr}` (top `{envl.top}`, sources {envl.sourceFiles.map (·.1)}). A literal `LeanModels.Sv.PDesign` — proofs may unfold it."
    -- The design family: named Nat binders in declaration order.
    let n := paramNames.length
    let natTy := Lean.mkConst ``Nat
    let intTy := Lean.mkConst ``Int
    let argsList := (List.range n).foldr
      (fun i acc => Lean.mkApp3 (Lean.mkConst ``List.cons [.zero]) intTy
        (Lean.mkApp (Lean.mkConst ``Int.ofNat) (Lean.mkBVar (n - 1 - i))) acc)
      (Lean.mkApp (Lean.mkConst ``List.nil [.zero]) intTy)
    let body := Lean.mkApp2 (Lean.mkConst ``LeanModels.Sv.PDesign.instantiateD)
      (Lean.mkConst pdName) argsList
    let value := paramNames.foldr
      (fun p acc => Lean.mkLambda (Name.mkSimple p) .default natTy acc) body
    let type := paramNames.foldr
      (fun p acc => Lean.mkForall (Name.mkSimple p) .default natTy acc)
      (Lean.mkConst ``LeanModels.Sv.Design)
    addAndCompile <| .defnDecl {
      name := funName
      levelParams := []
      type
      value
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst funName
    addDocStringCore funName
      s!"Design family `{envl.top}` (via `load_design_sv2` from `{pathStr}`): one `Nat` binder per SV parameter, declaration order — {paramNames}. Body: `PDesign.instantiateD {pdName}`; errors are the loud `errorDesign` (every run `.unsupported`), never silent."
    -- The semantic-tier twin: `name.sem : Nat^n → Design2` (phase 2 —
    -- selects, case, async reset; runs under `run2`).
    let semBody := Lean.mkApp2 (Lean.mkConst ``LeanModels.Sv.PDesign.instantiateD2)
      (Lean.mkConst pdName) argsList
    let semValue := paramNames.foldr
      (fun p acc => Lean.mkLambda (Name.mkSimple p) .default natTy acc) semBody
    let semType := paramNames.foldr
      (fun p acc => Lean.mkForall (Name.mkSimple p) .default natTy acc)
      (Lean.mkConst ``LeanModels.Sv.Design2)
    addAndCompile <| .defnDecl {
      name := semName
      levelParams := []
      type := semType
      value := semValue
      hints := .abbrev
      safety := .safe }
    enableRealizationsForConst semName
    addDocStringCore semName
      s!"Semantic-tier design family `{envl.top}` (`Design2`, via `PDesign.instantiateD2 {pdName}`): one `Nat` binder per SV parameter, declaration order — {paramNames}. Runs under `run2` (selects, case, async active-low reset in-tier)."
  liftTermElabM do
    Term.addTermInfo' name (Lean.mkConst funName) (isBinder := true)

/-! ## Inline smoke — hand-written sv-0.2 envelope only

(The real ff_one/alu_div envelopes are exercised from
`Examples/system-verilog/{ff_one,alu_div}/ingest.lean`, where the JSON is a
checked-in artifact; this file stays self-contained, the `Json.lean`
discipline.) The mini design `gen_cnt(W)` exercises: `ParameterDecl` +
`Int` default, `LocalParam` over `$clog2(ParamRef)`, `EnumType`/`TypeRef`/
`EnumRef`, symbolic `PackedType` bounds (`W-1:0` and `$clog2(W)-1:0`),
`Fill` initializer, `GenerateFor` + nested `GenerateIf` (with else), and a
`GenvarRef` in a value position. -/

private def miniEnvelopeText : String := r#"{
  "schema_version": "sv-0.2",
  "language": "systemverilog",
  "frontend": {"name": "pyslang", "version": "11.0.0"},
  "mode": "symbolic",
  "top": "gen_cnt",
  "source_files": [{"path": "gen_cnt.sv", "sha256": "0000000000000000000000000000000000000000000000000000000000000000"}],
  "packages": [],
  "design": {"kind": "Design", "modules": [
    {"kind": "Module", "span": null, "name": "gen_cnt",
     "imports": [],
     "params": [
       {"kind": "ParameterDecl", "span": null, "name": "W", "type": null,
        "default": {"kind": "Int", "span": null, "value": 8, "resolved_width": 32}, "resolved": 8},
       {"kind": "LocalParam", "span": null, "name": "NL", "type": null,
        "expr": {"kind": "SysCall", "span": null, "name": "$clog2",
                 "args": [{"kind": "ParamRef", "span": null, "name": "W"}], "resolved": 3},
        "resolved": 3}
     ],
     "types": [
       {"kind": "EnumType", "span": null, "name": "state_e", "from_package": null,
        "base_width": {"kind": "PackedType", "packed": [
          {"msb": {"kind": "Int", "span": null, "value": 1, "resolved_width": null},
           "lsb": {"kind": "Int", "span": null, "value": 0, "resolved_width": null}}], "resolved": 2},
        "members": [{"name": "IDLE", "value": 0}, {"name": "RUN", "value": 1}]}
     ],
     "ports": [
       {"kind": "Port", "span": null, "name": "a", "dir": "in",
        "width": {"kind": "PackedType", "packed": [
          {"msb": {"kind": "Binary", "span": null, "width": null, "op": "-",
                   "left": {"kind": "ParamRef", "span": null, "name": "W"},
                   "right": {"kind": "Int", "span": null, "value": 1, "resolved_width": null}},
           "lsb": {"kind": "Int", "span": null, "value": 0, "resolved_width": null}}], "resolved": 8}},
       {"kind": "Port", "span": null, "name": "cnt", "dir": "out",
        "width": {"kind": "PackedType", "packed": [
          {"msb": {"kind": "Binary", "span": null, "width": null, "op": "-",
                   "left": {"kind": "SysCall", "span": null, "name": "$clog2",
                            "args": [{"kind": "ParamRef", "span": null, "name": "W"}], "resolved": null},
                   "right": {"kind": "Int", "span": null, "value": 1, "resolved_width": null}},
           "lsb": {"kind": "Int", "span": null, "value": 0, "resolved_width": null}}], "resolved": 3}},
       {"kind": "Port", "span": null, "name": "st", "dir": "out",
        "width": {"kind": "TypeRef", "name": "state_e", "from_package": null, "resolved": 2}}
     ],
     "decls": [
       {"kind": "Var", "span": null, "name": "msk",
        "width": {"kind": "PackedType", "packed": [
          {"msb": {"kind": "Binary", "span": null, "width": null, "op": "-",
                   "left": {"kind": "ParamRef", "span": null, "name": "W"},
                   "right": {"kind": "Int", "span": null, "value": 1, "resolved_width": null}},
           "lsb": {"kind": "Int", "span": null, "value": 0, "resolved_width": null}}], "resolved": 8},
        "init": {"kind": "Fill", "span": null, "bit": "1", "resolved_width": 8}}
     ],
     "processes": [
       {"kind": "Assign", "span": null,
        "target": {"kind": "Ident", "span": null, "width": 2, "name": "st"},
        "value": {"kind": "EnumRef", "span": null, "type": "state_e", "member": "RUN", "from_package": null}}
     ],
     "generates": [
       {"kind": "GenerateFor", "span": null, "label": "g", "genvar": "i",
        "init": {"kind": "Int", "span": null, "value": 0, "resolved_width": 32},
        "bound": {"kind": "Binary", "span": null, "width": 1, "op": "s<",
                  "left": {"kind": "GenvarRef", "span": null, "name": "i"},
                  "right": {"kind": "ParamRef", "span": null, "name": "NL"}},
        "step": {"kind": "Unary", "span": null, "width": null, "op": "++",
                 "operand": {"kind": "GenvarRef", "span": null, "name": "i"}},
        "resolved_count": 3,
        "body": [
          {"kind": "GenerateIf", "span": null, "label": null, "else_label": null,
           "cond": {"kind": "Binary", "span": null, "width": 1, "op": "==",
                    "left": {"kind": "GenvarRef", "span": null, "name": "i"},
                    "right": {"kind": "Int", "span": null, "value": 0, "resolved_width": 32}},
           "then": [
             {"kind": "Assign", "span": null,
              "target": {"kind": "Ident", "span": null, "width": 3, "name": "cnt"},
              "value": {"kind": "GenvarRef", "span": null, "name": "i"}}],
           "else": null}
        ]}
     ],
     "others": []}
  ], "others": []},
  "lean_blocks": []
}"#

/-- What the mini envelope must parse to. -/
private def miniExpected : PDesign :=
  { name := "gen_cnt"
    params := [{ name := "W", default? := some (.int 8), resolved? := some 8 }]
    localParams := [{ name := "NL", expr := .sysCall .clog2 (.paramRef "W" none),
                      resolved? := some 3 }]
    enums := [{ name := "state_e", base := .packed [⟨.int 1, .int 0⟩] (some 2),
                members := [⟨"IDLE", .int 0⟩, ⟨"RUN", .int 1⟩] }]
    decls := [
      { name := "a", type := .packed [⟨.binary (.m0 .sub) (.paramRef "W" none) (.int 1), .int 0⟩] (some 8),
        isInput := true },
      { name := "cnt",
        type := .packed [⟨.binary (.m0 .sub) (.sysCall .clog2 (.paramRef "W" none)) (.int 1), .int 0⟩] (some 3),
        isOutput := true },
      { name := "st", type := .typeRef "state_e" none (some 2), isOutput := true },
      { name := "msk", type := .packed [⟨.binary (.m0 .sub) (.paramRef "W" none) (.int 1), .int 0⟩] (some 8),
        init := some (.fill .l1) }]
    processes := [.assign "st" (.enumRef "state_e" "RUN" none)]
    generates := [
      .genFor (some "g") "i" (.int 0)
        (.binary .slt (.genvarRef "i") (.paramRef "NL" none))
        (.unary .inc (.genvarRef "i")) (some 3)
        [.genIf (.binary (.m0 .eq) (.genvarRef "i") (.int 0))
          [.process (.assign "cnt" (.genvarRef "i"))]
          []]]
    others := [] }

#guard (loadPDesignString miniEnvelopeText).toOption == some miniExpected
#guard (parseEnvelope2String miniEnvelopeText).toOption.map (·.top) == some "gen_cnt"

-- The metadata cross-check at defaults is clean (what `load_design_sv2`
-- gates on).
#guard miniExpected.crossCheck == []

-- Instantiation at the default (W=8): widths a=8, cnt=clog2 8=3, st=2,
-- msk=8 with init '1 → 11111111; the generate family survives as exactly
-- one assign (i=0 branch), cnt = 0#3.
#guard miniExpected.instantiate [8] ==
  .ok { name := "gen_cnt"
        decls := #[
          { name := "a", width := 8, isInput := true },
          { name := "cnt", width := 3, isOutput := true },
          { name := "st", width := 2, isOutput := true },
          { name := "msk", width := 8, init := some (.replicate 8 .l1) }]
        processes := #[
          .assign "st" (.lit (.ofNat 2 1)),
          .assign "cnt" (.lit (.ofNat 3 0))] }

-- … and the instantiated design RUNS under the untouched M0 cycle
-- semantics, at two different parameter points of the same family.
#guard (Res.toOption (run (miniExpected.instantiateD [8]) σ_src 64 [[("a", LVec.ofNat 8 0)]])).map
        (fun tr => tr.map fun st => (SvState.showSignal st "st", SvState.showSignal st "cnt",
                                     SvState.showSignal st "msk"))
      == some [("01", "000", "11111111")]
#guard (Res.toOption (run (miniExpected.instantiateD [32]) σ_src 64 [[("a", LVec.ofNat 32 0)]])).map
        (fun tr => tr.map fun st => (SvState.showSignal st "cnt", SvState.showSignal st "msk"))
      == some [("00000", "11111111111111111111111111111111")]

-- Unsupported members route to `others` and stay LOUD: a module with an
-- out-of-tier member (an instance) parses, instantiates, and every run of
-- it is `.unsupported` — never silently dropped.
private def unsupMemberText : String := r#"{
  "schema_version": "sv-0.2",
  "language": "systemverilog",
  "frontend": {"name": "pyslang", "version": "11.0.0"},
  "mode": "symbolic",
  "top": "wrap",
  "source_files": [{"path": "wrap.sv", "sha256": "0000000000000000000000000000000000000000000000000000000000000000"}],
  "packages": [],
  "design": {"kind": "Design", "modules": [
    {"kind": "Module", "span": null, "name": "wrap",
     "imports": [], "params": [], "types": [],
     "ports": [{"kind": "Port", "span": null, "name": "y", "dir": "out",
                "width": {"kind": "PackedType", "packed": [], "resolved": 1}}],
     "decls": [],
     "processes": [],
     "generates": [],
     "others": [{"kind": "Unsupported", "span": null, "sv_kind": "InstanceSymbol:Instance", "text": "sub u0 (.y(y));"}]}
  ], "others": []},
  "lean_blocks": []
}"#

#guard (loadPDesignString unsupMemberText).toOption.map (·.others)
        == some [("InstanceSymbol:Instance", "sub u0 (.y(y));")]
#guard ((loadPDesignString unsupMemberText).toOption.map
          fun pd => run (pd.instantiateD []) σ_src 64 [[]])
        == some (.unsupported "unsupported process 'InstanceSymbol:Instance'")

-- Error paths stay loud and descriptive.
#guard (parseEnvelope2String "{\"schema_version\": \"sv-0.1\"}").isOk == false  -- M0 lane
#guard (Json.parse "{\"kind\": \"Spooky\"}" >>= parsePExpr).isOk == false
#guard (Json.parse r#"{"kind": "SysCall", "name": "$floor", "args": []}"# >>= parsePExpr).isOk == false
-- SysCall arity ≠ 1 is representable but loud (unsupported node, not a parse error).
#guard (Json.parse r#"{"kind": "SysCall", "name": "$size", "args": []}"# >>= parsePExpr).toOption
        == some (.unsupported "SysCall:arity" "$size with 0 args")

end LeanModels.Sv
