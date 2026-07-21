import LeanModels.Sv.Basic

/-!
# SV M0 design AST (`LeanModels.Sv`)

Lean inductives for the M0 language tier of `docs/sv-design-m0.md`: single
module, `logic`/`wire` declarations with optional initializers, four process
shapes, blocking/nonblocking assignment, `if`/`else`, `begin/end`, and the
M0 expression grammar. Anything outside the tier arrives as an
`unsupported` node (carrying the slang node class name and ≤200 chars of
source text) — ingestion never fails, the interpreter returns
`.unsupported` (loud) when such a node is reached.

Ordering is semantically significant everywhere an `Array` appears:
`Design.decls` and `Design.processes` are in **source/declaration order** —
the schedule oracle's executable default `σ_src` is exactly this order
(Xcelium empirically follows it for the M0 examples).

M0 has no bit/part-selects, so assignment targets are plain identifier
names (`String`), not expressions. Literal widths are already resolved by
the extractor (`8'd1`, `'0`, unsized — all arrive as an `LVec` of the
context-determined width).
-/

namespace LeanModels.Sv

/-- M0 unary operators: `~` (bitwise not), `!` (logical not), `-` (arith
negation). Evaluated by `LVec.not` / `LVec.lnot` / `LVec.neg`. -/
inductive UnaryOp where
  | bnot  -- `~`
  | lnot  -- `!`
  | neg   -- `-`
deriving Repr, BEq, DecidableEq, Inhabited

/-- M0 binary operators (`docs/sv-design-m0.md` expression tier):
`+ - & | ^ == != < <= > >=`. Case equality `===`/`!==` is NOT in the M0
expression tier (source uses of it arrive as `Expr.unsupported`); `LVec`
still implements it for the proof layer. Evaluated by `LVec.add/sub/and/or/
xor/eqLogical/neLogical/lt/le/gt/ge`. -/
inductive BinOp where
  | add   -- `+`
  | sub   -- `-`
  | and   -- `&`
  | or    -- `|`
  | xor   -- `^`
  | eq    -- `==`
  | ne    -- `!=`
  | lt    -- `<`
  | le    -- `<=`
  | gt    -- `>`
  | ge    -- `>=`
deriving Repr, BEq, DecidableEq, Inhabited

/-- M0 expressions. `lit` carries the fully resolved 4-state value (width
included — the extractor resolves `'0`/unsized literals to context width).
`concat` parts are in source order: `parts[0]` is the MOST significant
(evaluate with `LVec.concatMany`). `unsupported` carries the slang node
class name (`svKind`) and ≤200 chars of source text. -/
inductive Expr where
  | lit (value : LVec)
  | ident (name : String)
  | unary (op : UnaryOp) (arg : Expr)
  | binary (op : BinOp) (left right : Expr)
  | ternary (cond thenE elseE : Expr)
  | concat (parts : Array Expr)
  | unsupported (svKind : String) (text : String)
deriving Repr, BEq, Inhabited
-- DecidableEq deriving does not cope with the nested `Array Expr`; BEq suffices.

/-- M0 statements. Assignment targets are plain identifiers (no selects in
M0). An `ifStmt` with `elseBranch = none` is a NO-OP when the condition is
untrue (§12.4 — an x/z condition therefore HOLDS the target, latch-style,
never x-poisons it). `block` is `begin … end` (statements in source order). -/
inductive Stmt where
  | blockingAssign (target : String) (value : Expr)   -- `target = value;`
  | nbaAssign (target : String) (value : Expr)        -- `target <= value;`
  | ifStmt (cond : Expr) (thenBranch : Stmt) (elseBranch : Option Stmt)
  | block (body : Array Stmt)
  | unsupported (svKind : String) (text : String)
deriving Repr, BEq, Inhabited

/-- M0 processes. `alwaysFF` is `always_ff @(posedge clock)`; `alwaysPlain`
is plain `always @(posedge clock)` (same M0 cycle semantics, kept distinct
for fidelity to source); `alwaysComb` is `always_comb`; `assign` is a
continuous assignment (target a plain identifier in M0). Out-of-tier
processes (`initial`, `always_latch`, negedge/mixed sensitivity, …) arrive
as `unsupported`. -/
inductive Process where
  | alwaysFF (clock : String) (body : Stmt)
  | alwaysPlain (clock : String) (body : Stmt)
  | alwaysComb (body : Stmt)
  | assign (target : String) (value : Expr)
  | unsupported (svKind : String) (text : String)
deriving Repr, BEq, Inhabited

/-- One variable/net declaration. `width` is resolved (scalar `logic` = 1;
`logic [W-1:0]` = W). `init` is the (rare) declaration initializer, e.g.
`logic [7:0] a = 8'd1` — variables without one start all-x (§6.8).
Ports have `isInput`/`isOutput` set; internal signals have neither. -/
structure Decl where
  name : String
  width : Nat
  isInput : Bool := false
  isOutput : Bool := false
  init : Option LVec := none
deriving Repr, BEq, Inhabited

/-- A single elaborated M0 module. `decls` in declaration order (ports
first, in port-list order); `processes` in source order — `σ_src` is this
order. -/
structure Design where
  name : String
  decls : Array Decl
  processes : Array Process
deriving Repr, BEq, Inhabited

/-- Names of the input ports, in declaration order (the stimulus overwrite
in `cycleStep` targets exactly these). -/
def Design.inputNames (d : Design) : Array String :=
  d.decls.filterMap fun dc => if dc.isInput then some dc.name else none

/-- Names of the output ports, in declaration order. -/
def Design.outputNames (d : Design) : Array String :=
  d.decls.filterMap fun dc => if dc.isOutput then some dc.name else none

/-- `true` iff some node anywhere in the design is `unsupported` (handy for
harness-side early warning; the interpreter is loud regardless). -/
def Design.hasUnsupported (d : Design) : Bool :=
  d.processes.any fun p =>
    match p with
    | .unsupported _ _ => true
    | .alwaysFF _ s | .alwaysPlain _ s | .alwaysComb s => stmtHas s
    | .assign _ e => exprHas e
where
  exprHas : Expr → Bool
    | .unsupported _ _ => true
    | .lit _ | .ident _ => false
    | .unary _ a => exprHas a
    | .binary _ a b => exprHas a || exprHas b
    | .ternary c a b => exprHas c || exprHas a || exprHas b
    | .concat ps => ps.attach.any fun ⟨p, _⟩ => exprHas p
  stmtHas : Stmt → Bool
    | .unsupported _ _ => true
    | .blockingAssign _ e | .nbaAssign _ e => exprHas e
    | .ifStmt c t e =>
        exprHas c || stmtHas t || (match e with | some s => stmtHas s | none => false)
    | .block body => body.attach.any fun ⟨s, _⟩ => stmtHas s

/-! ## Smoke tests: hand-written `counter` and `race_blk` designs -/

/-- `Examples/sv/counter.sv`, hand-transcribed (the JSON-ingested version
lives in `Json.lean` tests). -/
private def counterDesign : Design :=
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

#guard counterDesign.inputNames == #["clk", "rst"]
#guard counterDesign.outputNames == #["count"]
#guard counterDesign.hasUnsupported == false

private def raceBlkDesign : Design :=
  { name := "race_blk"
    decls := #[
      { name := "clk", width := 1, isInput := true },
      { name := "a", width := 8, init := some (.ofNat 8 1) },
      { name := "b", width := 8, init := some (.ofNat 8 2) }]
    processes := #[
      .alwaysPlain "clk" (.blockingAssign "a" (.ident "b")),
      .alwaysPlain "clk" (.blockingAssign "b" (.ident "a"))] }

#guard raceBlkDesign.inputNames == #["clk"]
#guard raceBlkDesign.outputNames == (#[] : Array String)
#guard (raceBlkDesign.decls.filterMap Decl.init).map LVec.toBinString
        == #["00000001", "00000010"]

#guard Design.hasUnsupported
  { name := "bad", decls := #[]
    processes := #[.alwaysComb (.block #[.unsupported "ForLoopStatement" "for (...)"])] }

end LeanModels.Sv
