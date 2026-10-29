import Lean
import LeanModels.Sv.Param
import LeanModels.Sv.Param2
import LeanModels.Sv.Hier2
import LeanModels.Sv.Probe2
import LeanModels.Sv.RangeGuard2

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
deriving instance Lean.ToExpr for PartMode
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
deriving instance Lean.ToExpr for PPathSeg
deriving instance Lean.ToExpr for PConn
deriving instance Lean.ToExpr for PInst
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
  | "==?" => .ok (.m0 .wildEq) | "!=?" => .ok (.m0 .wildNe)
  | "<" => .ok (.m0 .lt) | "<=" => .ok (.m0 .le)
  | ">" => .ok (.m0 .gt) | ">=" => .ok (.m0 .ge)
  | "*" => .ok .mul | "/" => .ok .div | "%" => .ok .mod | "**" => .ok .pow
  | "u/" => .ok (.m0 .div) | "s/" => .ok (.m0 .sdiv)
  | "u%" => .ok (.m0 .rem) | "s%" => .ok (.m0 .srem)
  | "u**u" => .ok (.m0 (.pow false false)) | "u**s" => .ok (.m0 (.pow false true))
  | "s**u" => .ok (.m0 (.pow true false)) | "s**s" => .ok (.m0 (.pow true true))
  | "u<<" => .ok (.m0 (.shl false)) | "s<<" => .ok (.m0 (.shl true))
  | "u>>" => .ok (.m0 (.shr false)) | "s>>" => .ok (.m0 (.shr true))
  | "u<<<" => .ok (.m0 (.ashl false)) | "s<<<" => .ok (.m0 (.ashl true))
  | "u>>>" => .ok (.m0 (.ashr false)) | "s>>>" => .ok (.m0 (.ashr true))
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
        | some v =>
            -- A SIGNED literal (`4'sd3`, or a constant slang typed `int`;
            -- optional `signed: true`) is the cast `$signed(lit)`: the same
            -- bits, signed for every consuming operator — the value tier
            -- passes casts through, the constant tier reads them signed.
            match getOptField j "signed" with
            | some (Json.bool true) => return .cast true (.lit v)
            | none | some (Json.bool false) => return .lit v
            | some _ => throw "field 'signed' is not a bool"
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
    | "SignedResize" =>
        return .signedResize (← getNatField j "width") (← parsePExpr (← getField j "operand"))
    | "Squash2" =>
        -- 4-state → 2-state squash (2-state parameter/localparam types,
        -- e.g. `parameter int unsigned`): value-preserving in the constant
        -- tier and retained by the semantic-tier evaluator.
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
    | "ArraySel" =>
        -- A packed-array select path (raw declared labels; Param2 lowers
        -- it against the declaration's dimensions).
        let name ← getStrField j "name"
        let indices ← (← (← getField j "indices").getArr?).toList.mapM parsePExpr
        match getOptField j "part" with
        | none => return .arrayElem name indices
        | some pj =>
            let mode ← match ← getStrField pj "mode" with
              | "range" => pure PartMode.range
              | "up" => pure PartMode.up
              | "down" => pure PartMode.down
              | m => throw s!"unknown ArraySel part mode {m.quote}"
            return .arrayPart name indices mode (← parsePExpr (← getField pj "left"))
              (← parsePExpr (← getField pj "right"))
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

/-- Semantic-tier assignment targets: whole signal, one `BitSel`/`PartSel`
over an identifier base, a packed-array select path (`ArraySel`), or a
concatenation of those leaves. Anything else degrades to a loud unsupported
statement. -/
partial def parseTargetL (j : Json) : Except String (Except String PLhs) := do
  match (← j.getObjVal? "kind") with
  | .str "ConcatTarget" =>
      let parts ← match (← j.getObjVal? "parts").getArr? with
        | .ok xs => xs.toList.mapM parseTargetL
        | .error _ => throw "ConcatTarget.parts must be an array"
      if parts.isEmpty then return .error "AssignmentExpression:target"
      let mut lowered : List PLhs := []
      for part in parts do
        match part with
        | .ok p => lowered := lowered ++ [p]
        | .error e => return .error e
      return .ok (.concat lowered)
  | _ =>
      match ← parsePExpr j with
      | .ident n => return .ok (.ident n)
      | .bitSel (.ident n) idx => return .ok (.bitSel n idx)
      | .partSel (.ident n) msb lsb => return .ok (.partSel n msb lsb)
      | .arrayElem n is => return .ok (.arrayElem n is)
      | .arrayPart n is mode a b => return .ok (.arrayPart n is mode a b)
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

/-! ## Module instances (F3) -/

/-- One `PortConn` (or a loud `Unsupported` connection). An unconnected
input carries `net` (an unconnected net reads z, a variable x). -/
def parsePConn (j : Json) : Except String PConn := do
  match ← getKind j with
  | "PortConn" =>
      let port ← getStrField j "port"
      withCtx s!"port '{port}'" do
        match ← getStrField j "dir" with
        | "in" =>
            match getOptField j "expr" with
            | some ej => return .input port (some (← parsePExpr ej)) false
            | none =>
                match getOptField j "net" with
                | some (Json.bool b) => return .input port none b
                | _ => throw "unconnected input without a boolean 'net' field"
        | "out" =>
            match getOptField j "target" with
            | none => return .output port none
            | some tj =>
                match ← parseTargetL tj with
                | .ok t => return .output port (some t)
                | .error k => return .unsupported port k "output port connection target"
        | d => throw s!"unknown port connection dir {d.quote}"
  | "Unsupported" =>
      let (svKind, text) ← parseUnsupportedFields j
      return .unsupported "" svKind text
  | other => throw s!"unknown port connection kind {other.quote}"

/-- An `Instance` node: definition name, lexical generate path, overridden
parameters (symbolic constant expressions of the instantiating scope), one
connection per child port. -/
def parsePInst (j : Json) : Except String PInst := do
  let name ← getStrField j "name"
  withCtx s!"instance '{name}'" do
    let module ← getStrField j "module"
    let path ← (← (← getField j "path").getArr?).toList.mapM fun sj => do
      pure { label := ← getStrField sj "label", genvar := getOptStr sj "genvar" : PPathSeg }
    let params ← (← (← getField j "params").getArr?).toList.mapM fun pj => do
      let pname ← getStrField pj "name"
      pure (pname, ← withCtx s!"override '{pname}'" (parsePExpr (← getField pj "expr")))
    let conns ← (← (← getField j "ports").getArr?).toList.mapM parsePConn
    return { name, module, path, params, conns }

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
    | "Instance" => return .inst (← parsePInst j)
    | "Var" | "Net" | "LocalParam" | "ParameterDecl" =>
        -- Generate-local declarations — including a `localparam` in a
        -- generate block (per-instance constant scoping) — are outside this
        -- slice: a loud item, never a whole-envelope parse failure.
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
      let isSigned := match getOptField j "signed" with
        | none => false
        | some value => value.getBool?.toOption.getD false
      let twoState := match getOptField j "two_state" with
        | none => false
        | some value => value.getBool?.toOption.getD false
      match kind with
      | "Port" =>
          -- An OUTPUT variable port's declaration initializer (`output
          -- logic [1:0] y = 2'b10`; round 3 CX repair — the extractor
          -- used to drop it silently) is its initial value, exactly a
          -- `Var`'s `init`. An input port never carries one (a port
          -- default is refused at the unconnected connection): loud.
          let init ← match getOptField j "init" with
            | none => pure none
            | some ji => pure (some (← withCtx "init" (parsePExpr ji)))
          match ← getStrField j "dir" with
          | "in" =>
              if init.isSome then throw "input port with an initializer (a port default) is outside the tier"
              return { name, type := ty, isSigned, twoState, isInput := true }
          | "out" => return { name, type := ty, isSigned, twoState, isOutput := true, init }
          | d => throw s!"unknown port dir {d.quote}"
      | "Var" | "Net" =>
          let init ← match getOptField j "init" with
            | none => pure none
            | some ji => pure (some (← withCtx "init" (parsePExpr ji)))
          return { name, type := ty, isSigned, twoState, isNet := kind == "Net", init }
      | other => throw s!"unknown declaration kind {other.quote}"

/-- The optional `signed` field of a `ParameterDecl`/`LocalParam` (the
declared type's signedness when it departs from the envelope default —
`PParam.signed?`). -/
private def parseOptSigned (j : Json) : Except String (Option Bool) :=
  match getOptField j "signed" with
  | none => .ok none
  | some (Json.bool b) => .ok (some b)
  | some _ => .error "field 'signed' is not a bool"

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
          let signed? ← parseOptSigned pj
          params := params ++
            [{ name := pname, default?, resolved? := getOptInt pj "resolved", type?, signed? }]
      | "LocalParam" =>
          let pname ← getStrField pj "name"
          let expr ← withCtx s!"localparam '{pname}'" (parsePExpr (← getField pj "expr"))
          let type? ← match getOptField pj "type" with
            | none => pure none
            | some tj => pure (some (← withCtx s!"localparam '{pname}' type" (parsePType tj)))
          let signed? ← parseOptSigned pj
          localParams := localParams ++
            [{ name := pname, expr, resolved? := getOptInt pj "resolved", type?, signed? }]
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
  /-- The module library of a hierarchical envelope (F3): the definitions
  of every module the top instantiates, transitively, each elaborated alone
  at its own defaults (`[]` for a single-module envelope). -/
  lib : List PDesign := []
deriving Repr, BEq, Inhabited

/-- Parse a full sv-0.2 envelope. Validates `schema_version = "sv-0.2"`,
`language = "systemverilog"`, `mode = "symbolic"`, loudly. The first module
is the top; the further ones are the module library of a hierarchical
design (F3). -/
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
    | m :: defs =>
        let pd ← parseModule2 m
        unless pd.name == top do
          throw s!"module name {pd.name.quote} ≠ top {top.quote}"
        let lib ← defs.mapM fun dj => do
          let c ← parseModule2 dj
          pure c.markOverrideRetypes
        -- Untyped parameters whose default-point type an integer override
        -- changes (§6.20.2): value-position reads of them are loud at
        -- overridden points (`PParam.overrideRetypes`).
        return { top, sourceFiles, packages, design := pd.markOverrideRetypes, lib }
    | [] => throw "expected at least one module, got 0"

/-- JSON text → `Envelope2`. -/
def parseEnvelope2String (s : String) : Except String Envelope2 :=
  Json.parse s >>= parseEnvelope2

/-- JSON text → `PDesign`. -/
def loadPDesignString (s : String) : Except String PDesign :=
  (·.design) <$> parseEnvelope2String s

/-- JSON text → the top `PDesign` and its module library (`[]` for a
single-module envelope). -/
def loadHierString (s : String) : Except String (PDesign × List PDesign) :=
  (fun e => (e.design, e.lib)) <$> parseEnvelope2String s

/-! ## Probe sidecars (the multi-point cross-check, round 3 CX)

`extract.py --top T --probe-points "N=1;N=4,W=8"` writes, next to the
envelope `<file>.sv.json`, the sidecar `<file>.sv.probes.json` (schema
`sv-0.2-probes`, `docs/sv-envelope-schema.md` "Probe sidecar"): per point
the overrides, slang's error count there, the top module extracted AT the
point, and every probed instance. `Probe2.lean` holds the check; this
section parses sidecars and wires them into `load_design_sv2`, the
differential runner and the svGolf checker. -/

/-- `[{name, value}]` → override list (declaration order as written). -/
private def parseOverrides (j : Json) : Except String (List (String × Int)) := do
  (← j.getArr?).toList.mapM fun oj => do
    pure (← getStrField oj "name", ← getIntField oj "value")

/-- A probed module node, or `none` when the extractor recorded none (or
an out-of-vocabulary node — an unprobed entry, never agreement). The
module is marked exactly as `parseEnvelope2` marks every module. -/
private def parseProbeModule? (j : Option Json) : Except String (Option PDesign) :=
  match j with
  | none => .ok none
  | some mj =>
      match getKind mj with
      | .ok "Module" => do
          let pd ← parseModule2 mj
          pure (some pd.markOverrideRetypes)
      | _ => .ok none

/-- Parse a probe sidecar. Validates `schema_version = "sv-0.2-probes"`,
loudly; a point whose top module did not extract as a `Module` fails the
parse (a refusal, never a vacuous point). -/
def parseProbes2 (j : Json) : Except String Probes2 :=
  withCtx "probe sidecar" do
    let sv ← getStrField j "schema_version"
    unless sv == "sv-0.2-probes" do
      throw s!"unsupported schema_version {sv.quote} (want \"sv-0.2-probes\")"
    let top ← getStrField j "top"
    let sourceFiles ← (← (← getField j "source_files").getArr?).toList.mapM fun sj => do
      pure (← getStrField sj "path", ← getStrField sj "sha256")
    let points ← (← (← getField j "points").getArr?).toList.mapM fun pj => do
      let overrides ← withCtx "point" (parseOverrides (← getField pj "overrides"))
      withCtx s!"point {renderOverrides overrides}" do
        let frontendErrors := (getOptNat pj "frontend_errors").getD 0
        let some module ← parseProbeModule? (getOptField pj "module")
          | throw "the top module did not extract at this point"
        let instances ← match getOptField pj "instances" with
          | none => pure []
          | some ij => (← ij.getArr?).toList.mapM fun ej => do
              let mname ← getStrField ej "module"
              let ov ← match getOptField ej "overrides" with
                | none => pure none
                | some oj => some <$> parseOverrides oj
              let design ← parseProbeModule? (getOptField ej "design")
              pure ({ module := mname, overrides := ov, design } : ProbeInst2)
        pure ({ overrides, frontendErrors, module, instances } : ProbePoint2)
    return { top, sourceFiles, points }

/-- JSON text → `Probes2`. -/
def parseProbes2String (s : String) : Except String Probes2 :=
  Json.parse s >>= parseProbes2

/-- The sidecar path of an envelope path: `x.sv.json` ↦ `x.sv.probes.json`. -/
def probeSidecarPath (envPath : String) : String :=
  if envPath.endsWith ".json" then
    String.join ((envPath.toList.take (envPath.length - 5)).map Char.toString) ++ ".probes.json"
  else envPath ++ ".probes.json"

/-- Every probe verdict of a sidecar against its envelope, labelled
`<point> <entry>` (`Probes2.report`). -/
def Envelope2.probeReport (e : Envelope2) (pr : Probes2) : List (String × ProbeVerdict) :=
  pr.report e.top e.sourceFiles e.design e.lib

/-- **The svGolf checker's entry point** (pure): envelope text and probe
sidecar text → every verdict (`Envelope2.probeReport`). `.ok` lists every
entry; the design passes the cross-check iff all are `.agree`
(`ProbeVerdict.ok`); `.error` = an unparseable envelope or sidecar. -/
def probeReportString (envText probesText : String) :
    Except String (List (String × ProbeVerdict)) := do
  let e ← parseEnvelope2String envText
  let pr ← parseProbes2String probesText
  return e.probeReport pr

/-- **The legacy-select range guard at every probed point** (round 3
folds, `RangeGuard2.lean`): the first point at which a module of the
hierarchy selects a declaration with the legacy offset encoding while its
range there is not `[m:0]`, `m ≥ 0` — `(point, message)`, or `none`. A
point the envelope cannot be brought to (`PDesign.atPoint`) is left to the
cross-check, which refuses it. -/
def Envelope2.legacyRangeAtPoints (e : Envelope2) (pr : Probes2) : Option (String × String) :=
  pr.points.findSome? fun p =>
    match e.design.atPoint (e.design.params.map fun prm => p.overrides.lookup prm.name) with
    | .ok (d', args) => (d'.legacyRangeReport e.lib args).map (renderOverrides p.overrides, ·)
    | .error _ => none

/-- `probeReportString` collapsed to pass/fail: `.ok n` = all `n` entries
agree, `.error msg` = the first failing entry (or a parse error). Since
round 3 (folds) also `.error` when the legacy-select range guard refuses
at a probed point (`Envelope2.legacyRangeAtPoints`). -/
def probeCheckString (envText probesText : String) : Except String Nat := do
  let rep ← probeReportString envText probesText
  match rep.find? (fun (_, v) => !v.ok) with
  | some (l, v) => throw s!"cross-check FAILED at {l}: {v.render}"
  | none =>
      let e ← parseEnvelope2String envText
      let pr ← parseProbes2String probesText
      match e.legacyRangeAtPoints pr with
      | some (l, msg) => throw s!"range guard FAILED at {l}: {msg} (`Select:legacy-range`)"
      | none => return rep.length

/-- `probeCheckString` on files: the envelope at `envPath` and its sidecar
(`probeSidecarPath`). `.ok none` = no sidecar exists (nothing checked —
NOT agreement; a checker that requires the cross-check must treat it as a
failure), `.ok (some n)` = all `n` entries agree. -/
def probeCheckFile (envPath : System.FilePath) : IO (Except String (Option Nat)) := do
  let side : System.FilePath := ⟨probeSidecarPath envPath.toString⟩
  unless (← side.pathExists) do return .ok none
  let envText ← IO.FS.readFile envPath
  let prText ← IO.FS.readFile side
  return (some <$> probeCheckString envText prText)

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
* `ff_one.sem : Nat → … → Nat → Design2` — the semantic-tier twin
  (`PDesign.instantiateGD2`: `PDesign.instantiateD2` under the one-driver
  rule `driversOk` — continuous drivers, the §6.5 continuous/procedural
  mixture and the `always_comb`/`always_ff` exclusivity, per window —
  checked at EVERY parameter point — a violation is the
  loud `PortConn:driver` process, `Hier2.lean` "Drivers"; at the defaults
  the envelope is refused here); for a HIERARCHICAL envelope (F3: the top plus
  the definitions it instantiates) also `ff_one.plib : List PDesign`, the
  module library, and `ff_one.sem` flattens through
  `PDesign.instantiateHD2 ff_one.pdesign ff_one.plib` (`Hier2.lean`); every
  library module passes the same `crossCheck` gate at its own defaults, and
  the hierarchy flattened at the defaults must have distinct names
  (`Design2.namesNodup`) and one driver per bit (`driversOk`: no
  `PortConn:driver` process).

Before defining anything the command replays the defaults elaboration and
compares it against the envelope's `resolved` metadata
(`PDesign.crossCheck`); any mismatch **refuses the envelope** with the
full message list — the ingestion-time differential test against slang.
When the envelope has a probe sidecar (`x.sv.json` ↦ `x.sv.probes.json`,
written by `extract.py --probe-points`), every entry of it must
`agree` (`Probe2.lean`, the multi-point cross-check: the envelope and
slang's own extraction AT each point instantiate to the same design there,
and slang's metadata at the point matches the Lean elaboration); the first
entry that does not refuses the envelope, naming the point, the entry and
the first difference.
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
  -- A hierarchical envelope (F3): every library module passes the same
  -- differential gate against ITS defaults (the extractor elaborated each
  -- definition alone at its own defaults).
  let lib := envl.lib
  for c in lib do
    match c.crossCheck with
    | [] => pure ()
    | msgs =>
        throwErrorAt path
          "load_design_sv2: '{pathStr}' REFUSED — module '{c.name}' of the hierarchy: our defaults elaboration disagrees with the envelope's `resolved` metadata (Lean vs slang differential):\n  {String.intercalate "\n  " msgs}"
  -- The defaults point with exact 32-bit `int` constants (`int32Agrees`).
  match pd.atPoint [] with
  | .ok (pdD, argsD) =>
      unless (if lib.isEmpty then pdD.int32Agrees argsD else pdD.int32AgreesH lib argsD) do
        throwErrorAt path
          "load_design_sv2: '{pathStr}' REFUSED — at the defaults an INT-class constant expression leaves the 32-bit range: exact 32-bit `int` arithmetic and the unbounded constant tier build different designs (`PDesign.int32Agrees`)"
      -- Every top, flat ones included (2026-10-28, WP2): an instance-free
      -- top through `instantiateG2` (`name.sem`'s family), a hierarchical
      -- one through `instantiateH` (whose `topGuard` checks it).
      let flatTop := lib.isEmpty || GenItem.listInstFree pdD.generates
      let instD := if flatTop then pdD.instantiateG2 argsD (PDesign.surfaceFuel argsD)
        else pdD.instantiateH lib argsD (PDesign.surfaceFuel argsD)
      match instD with
      | .ok dD =>
          unless lib.isEmpty || dD.namesNodup do
            throwErrorAt path
              "load_design_sv2: '{pathStr}' REFUSED — flattening the hierarchy at the defaults produced two declarations of one name (`Design2.namesNodup`)"
          -- The one-driver rule (`Hier2.lean`, "Drivers"): a design that
          -- violates it AT THE DEFAULTS is refused here, early; at any
          -- other point `name.sem` carries the loud `PortConn:driver`.
          for p in dD.processes do
            match p with
            | .unsupported "PortConn:driver" msg =>
                throwErrorAt path
                  "load_design_sv2: '{pathStr}' REFUSED — at the defaults, {msg} (`PortConn:driver`, `driversOk`)"
            -- The always_comb self-read guard (WP4, `CombGuard2.lean`):
            -- refused here at the defaults, loud in `name.sem` elsewhere.
            | .unsupported "AlwaysComb:self-read" msg =>
                throwErrorAt path
                  "load_design_sv2: '{pathStr}' REFUSED — at the defaults, in the instantiated design of module '{dD.name}': {msg} (`AlwaysComb:self-read`, `Stmt2.combAdmits`)"
            | _ => pure ()
      | _ => pure ()
      -- The legacy-select range guard (round 3 folds, `RangeGuard2.lean`):
      -- a check BESIDE `name.sem` (whose recorded lemmas pin it), run at
      -- the defaults here and at every probed point below.
      if let some msg := pdD.legacyRangeReport lib argsD then
        throwErrorAt path
          "load_design_sv2: '{pathStr}' REFUSED — at the defaults, {msg} (`Select:legacy-range`, `PDesign.legacyRangeReport`)"
  | .error _ => pure ()
  -- The multi-point cross-check (round 3 CX, `Probe2.lean`): when the
  -- envelope has a probe sidecar (`extract.py --probe-points`), every
  -- point's re-extraction must instantiate to exactly the design the
  -- envelope gives there — a default-point fold differs, and refuses here.
  let sidePath := probeSidecarPath pathStr
  if ← System.FilePath.pathExists ⟨sidePath⟩ then
    let prText ←
      match ← (IO.FS.readFile ⟨sidePath⟩).toBaseIO with
      | .ok c => pure c
      | .error e => throwErrorAt path "load_design_sv2: cannot read probe sidecar '{sidePath}': {toString e}"
    match parseProbes2String prText with
    | .error e =>
        throwErrorAt path "load_design_sv2: '{pathStr}' REFUSED — its probe sidecar '{sidePath}' is not valid: {e}"
    | .ok pr =>
        match (envl.probeReport pr).find? (fun (_, v) => !v.ok) with
        | some (l, v) =>
            throwErrorAt path
              "load_design_sv2: '{pathStr}' REFUSED — multi-point cross-check (probe sidecar '{sidePath}') at {l}: {v.render}\n({v.meaning} — `Probe2.lean`)"
        | none => pure ()
        -- The legacy-select range guard at every probed point (round 3
        -- folds): the svGolf checker always probes the task's probe,
        -- scoring and backstop points.
        if let some (l, msg) := envl.legacyRangeAtPoints pr then
          throwErrorAt path
            "load_design_sv2: '{pathStr}' REFUSED — at the probed point {l}: {msg} (`Select:legacy-range`, `PDesign.legacyRangeReport`)"
  let funName := (← getCurrNamespace) ++ name.getId
  let pdName := funName ++ `pdesign
  let semName := funName ++ `sem
  let libName := funName ++ `plib
  for n in [funName, pdName, semName] ++ (if lib.isEmpty then [] else [libName]) do
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
    -- A hierarchical envelope's module library (F3): `name.plib`.
    unless lib.isEmpty do
      addAndCompile <| .defnDecl {
        name := libName
        levelParams := []
        type := Lean.mkApp (Lean.mkConst ``List [.zero]) (Lean.mkConst ``LeanModels.Sv.PDesign)
        value := toExpr lib
        hints := .abbrev
        safety := .safe }
      enableRealizationsForConst libName
      addDocStringCore libName
        s!"Module library of the hierarchical design `{envl.top}` (via `load_design_sv2` from `{pathStr}`): the definitions it instantiates, transitively — {lib.map (·.name)}. Each a literal `LeanModels.Sv.PDesign` elaborated alone at its own defaults."
    -- The semantic-tier twin: `name.sem : Nat^n → Design2` (phase 2 —
    -- selects, case, async reset; runs under `run2`). A hierarchical
    -- envelope flattens through `PDesign.instantiateHD2` (Hier2.lean); an
    -- instance-free top instantiates through `PDesign.instantiateGD2`,
    -- `instantiateD2` under the one-driver rule at every parameter point
    -- (2026-10-28, WP2 — `Hier2.lean`, "Drivers").
    let flatTop := lib.isEmpty || GenItem.listInstFree pd.generates
    let semBody :=
      if flatTop then
        Lean.mkApp2 (Lean.mkConst ``LeanModels.Sv.PDesign.instantiateGD2)
          (Lean.mkConst pdName) argsList
      else
        Lean.mkApp3 (Lean.mkConst ``LeanModels.Sv.PDesign.instantiateHD2)
          (Lean.mkConst pdName) (Lean.mkConst libName) argsList
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
      (if flatTop then
        s!"Semantic-tier design family `{envl.top}` (`Design2`, via `PDesign.instantiateGD2 {pdName}` — `instantiateD2` under the one-driver rule, Hier2.lean): one `Nat` binder per SV parameter, declaration order — {paramNames}. Runs under `run2` (selects, case, async active-low reset in-tier)."
      else
        s!"Semantic-tier design family `{envl.top}` (`Design2`, via `PDesign.instantiateHD2 {pdName} {libName}` — the module hierarchy flattened, Hier2.lean): one `Nat` binder per SV parameter, declaration order — {paramNames}. Runs under `run2`.")
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
-- A `localparam` inside a generate block is a loud item, not a parse failure.
#guard (Json.parse r#"{"kind": "LocalParam", "span": null, "name": "LL", "type": null,
    "expr": {"kind": "Int", "span": null, "value": 1, "resolved_width": 32}, "resolved": 1}"#
    >>= parseGenItem).toOption
        == some (.unsupported "GenerateDecl:LocalParam" "generate-local declaration 'LL'")
-- A signed literal (`signed: true`, symbolic constant positions) is
-- `$signed` of its bits; the optional typed-parameter `signed` field parses.
#guard (Json.parse r#"{"kind": "Literal", "span": null, "width": 4, "bits": "1111", "signed": true}"#
    >>= parsePExpr).toOption == some (.cast true (.lit (LVec.ofNat 4 15)))
#guard (Json.parse r#"{"kind": "Literal", "span": null, "width": 4, "bits": "1111"}"#
    >>= parsePExpr).toOption == some (.lit (LVec.ofNat 4 15))

end LeanModels.Sv
