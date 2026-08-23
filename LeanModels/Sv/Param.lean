import LeanModels.Sv.Obs
import LeanModels.Sv.Sem2

/-!
# SV parametric design layer (`LeanModels.Sv` — schema sv-0.2, phase 2)

The Lean side of the CV32E40P phase-1 symbolic envelopes
(`docs/sv-envelope-schema.md`, "Symbolic mode — schema sv-0.2"): a
**parametric** design AST (`PDesign`) whose parameters stay symbolic and
whose generate constructs stay structural, plus the proof-relevant
elaboration function

```
PDesign.instantiate : PDesign → List Int → (iterFuel : Nat) → Res Design
```

that substitutes concrete parameter values and expands `GenerateFor`
families into the **existing M0 `Design`** — so instantiated designs run
under the untouched M0 cycle semantics (`Semantics.lean`), and everything
outside the M0 tier arrives there as loud `.unsupported` nodes exactly as
before. This file deliberately imports no `Lean.Json`: JSON ingestion of
sv-0.2 envelopes lives in `Ingest2.lean`; theorems only ever mention the
types and functions here.

Design laws implemented (the point of the program):

* **Parameters stay symbolic.** A parameterized module is data
  (`PDesign`); a Design-valued *function* of its parameters is
  `fun args => d.instantiateD args` (the `load_design_sv2` command in
  `Ingest2.lean` binds it with named `Nat` binders in declaration order).
  ∀-parameter theorems quantify over the arguments of `instantiate`.
* **Generate stays structural.** `GenItem.genFor` is ONE constructor
  (genvar, symbolic init/bound/step, body template). Expansion is
  recursion over the genvar value sequence (`genvarSeq`), so proofs about
  generate families go by induction on that sequence — the
  `expandIters_*` and `genvarSeq_*` lemmas below are the induction
  handles (the analog lane's `chain : Nat → Netlist` precedent,
  `LeanModels/Spice/RippleNetlist.lean`, generalized to source-extracted
  families).

Representation deviations from the M0 `Ast.lean` conventions, both
deliberate: (1) the parametric layer uses **`List`** (not `Array`) for
every recursive field — nested-inductive structural recursion and the
expansion lemmas are far cleaner over `List`, and `instantiate` converts
to `Array` at the M0 boundary; (2) `SysCall` carries exactly **one**
argument (all four supported system functions are unary; the parser
enforces arity).

## Semantic decisions (the honest ledger)

* **Constant tier** (`evalInt`): parameter defaults, localparams,
  generate headers/conditions, dimension bounds evaluate over
  **mathematical `Int`** (SV value parameters are 32-bit signed ints; no
  CV32E40P parameter exceeds them). `/` `%` truncate toward zero
  (`Int.tdiv`/`Int.tmod`, the SV rule), `**` requires a nonnegative
  exponent, `>>` requires a nonnegative operand (logical shift of a
  negative constant is width-dependent — loud error instead), `>>>` is
  arithmetic (`Int.fdiv`). Signed comparisons (`s<` …) and the plain M0
  comparisons both compare mathematical values — at `Int` level the
  distinction is width information the constant tier does not carry
  (slang marks genuinely signed compares `s<`; nothing unsigned-negative
  can reach the plain ones from these envelopes).
* **`$clog2`** is `Sv.clog2` (ceiling log2, `clog2 0 = clog2 1 = 0` —
  the LRM's `$clog2`); **`$bits`/`$size`** of a *declared signal* is its
  instantiated width; **`$high`** of a declared signal is `width - 1`
  (the tier's packed ranges are `[W-1:0]`). Anything else (type
  arguments, expression arguments) is a loud error.
* **Widths.** Declared widths come from the symbolic `PackedType` bounds
  (`|msb - lsb| + 1` per dimension, multi-dim = product — a packed array
  is one bit vector). Declarations elaborate **in order**: a
  `$bits`/`$high` in a bound may reference earlier declarations only.
* **Value positions** instantiate context-width-directed: `Int`/`Fill`/
  `ParamRef`/`GenvarRef` literals materialize at the context width
  (assignment target's declared width; operands of arithmetic inherit
  it; comparison operands take the max of the operand self-widths — the
  LRM §11.6 rules restricted to this vocabulary; a fill with no
  determinable width is loud). Symbolic-only operators (`* / % ** <<
  …`), in a value position, constant-fold when closed over
  parameters and are loud otherwise (T-ops tier).
* **`Resize`** (width-changing implicit conversion, unsigned): its
  envelope width is **default-elaborated** (slang folds the target
  type), so it is honored only when it matches the context width at the
  *current* parameters — zero-extension becomes an M0 `concat` with a
  zero literal; truncation and any width mismatch are loud
  (`Resize:truncate` / `Resize:context`). This is a recorded envelope
  limitation, not paper-over: at non-default parameters the affected
  expression is `.unsupported`, never silently mis-sized.
* **`Squash2`** (4-state → 2-state) is outside the M0 value core — loud.
* **Enums** bind as literal values at the enum's base width (`EnumRef` →
  `Expr.lit`); the member table is data, never folded away at parse
  time.
* **Generate-local declarations** are outside this slice (they need
  per-instance name scoping) — they arrive as loud items. Neither smoke
  envelope contains one.
* **Package-scoped `ParamRef`** values are not in the envelope — loud at
  use (`ParamRef:package`).
* `instantiate` is **fueled only where unbounded**: the genvar iteration
  (`genvarSeq`, fuel exhausted = `.timeout`); everything else is
  structural recursion. Bad parameters (arity, failing localparam/width/
  bound evaluation) are `.unsupported` with a message — loud `Res`, the
  M0 discipline.
-/

namespace LeanModels.Sv

/-! ## `$clog2` and integer-valued vector embedding -/

/-- Ceiling log2 — the LRM's `$clog2`: least `k` with `n ≤ 2^k`
(`clog2 0 = clog2 1 = 0`). -/
def clog2 (n : Nat) : Nat := if n ≤ 1 then 0 else (n - 1).log2 + 1

#guard clog2 0 == 0
#guard clog2 1 == 0
#guard clog2 2 == 1
#guard clog2 3 == 2
#guard clog2 8 == 3
#guard clog2 9 == 4
#guard clog2 32 == 5
#guard clog2 33 == 6

/-- Two's-complement embedding of an `Int` at width `w` (negative values
wrap mod `2^w`, the SV rule for sized contexts). -/
def LVec.ofInt (w : Nat) (v : Int) : LVec := .ofNat w (v.emod ((2 : Int) ^ w)).toNat

#guard (LVec.ofInt 4 5).toBinString == "0101"
#guard (LVec.ofInt 4 (-1)).toBinString == "1111"
#guard (LVec.ofInt 4 (-8)).toBinString == "1000"
#guard (LVec.ofInt 8 256).toBinString == "00000000"

/-! ## The symbolic vocabulary -/

/-- Binary operators of the sv-0.2 envelope: the M0 set (`.m0`), the
symbolic-position extras (`* / % ** << >> <<< >>>`), signed order
comparisons (spelled `s<` … by the extractor), and the self-check-tier
extras (`=== !== && ||`, representable but outside the M0 value core). -/
inductive SymBinOp where
  | m0 (op : BinOp)
  | mul   -- `*`
  | div   -- `/`
  | mod   -- `%`
  | pow   -- `**`
  | shl   -- `<<`
  | shr   -- `>>`
  | ashl  -- `<<<`
  | ashr  -- `>>>`
  | slt   -- `s<`  (signed `<`)
  | sle   -- `s<=`
  | sgt   -- `s>`
  | sge   -- `s>=`
  | ceq   -- `===`
  | cne   -- `!==`
  | land  -- `&&`
  | lor   -- `||`
deriving Repr, BEq, DecidableEq, Inhabited

/-- Envelope spelling of a `SymBinOp` (error messages / parser table). -/
def SymBinOp.sym : SymBinOp → String
  | .m0 .add => "+" | .m0 .sub => "-" | .m0 .and => "&" | .m0 .or => "|"
  | .m0 .xor => "^" | .m0 .eq => "==" | .m0 .ne => "!=" | .m0 .lt => "<"
  | .m0 .le => "<=" | .m0 .gt => ">" | .m0 .ge => ">="
  | .mul => "*" | .div => "/" | .mod => "%" | .pow => "**"
  | .shl => "<<" | .shr => ">>" | .ashl => "<<<" | .ashr => ">>>"
  | .slt => "s<" | .sle => "s<=" | .sgt => "s>" | .sge => "s>="
  | .ceq => "===" | .cne => "!==" | .land => "&&" | .lor => "||"

/-- Unary operators: the M0 set plus unary `+` and the generate-step
`++`/`--` (which are legal only in `GenerateFor.step` position). -/
inductive SymUnaryOp where
  | m0 (op : UnaryOp)
  | plus  -- unary `+` (identity)
  | inc   -- `++` (generate step only)
  | dec   -- `--` (generate step only)
deriving Repr, BEq, DecidableEq, Inhabited

/-- The four sv-0.2 system functions (expression position, one argument). -/
inductive SysFn where
  | clog2 | bits | high | size
deriving Repr, BEq, DecidableEq, Inhabited

def SysFn.sym : SysFn → String
  | .clog2 => "$clog2" | .bits => "$bits" | .high => "$high" | .size => "$size"

/-- Symbolic expressions — the sv-0.2 expression vocabulary. One type for
every expression position (process values, parameter defaults, generate
headers, dimension bounds); the two evaluation modes are `evalInt`
(constant tier, `Int`-valued) and `instExpr` (value tier, → M0 `Expr`). -/
inductive PExpr where
  /-- Sized 4-state literal (already width-resolved by the extractor). -/
  | lit (value : LVec)
  /-- Signal reference. -/
  | ident (name : String)
  /-- Parameter/localparam reference; `pkg` is set only for package-scoped
  parameters (whose values the envelope does not carry — loud at use). -/
  | paramRef (name : String) (pkg : Option String)
  /-- Enclosing generate-for loop variable reference. -/
  | genvarRef (name : String)
  /-- Enum member used as a value (`type` is the `PEnumType` name). -/
  | enumRef (type member : String) (pkg : Option String)
  /-- Unsized integer literal (32-bit signed int; materializes at context
  width). -/
  | int (value : Int)
  /-- Unbased-unsized literal `'0`/`'1`/`'x`/`'z` — width is context-
  determined, potentially parameter-dependent. -/
  | fill (bit : Logic)
  | unary (op : SymUnaryOp) (arg : PExpr)
  | binary (op : SymBinOp) (left right : PExpr)
  | ternary (cond thenE elseE : PExpr)
  /-- Source order, `parts[0]` most significant (M0 convention). -/
  | concat (parts : List PExpr)
  /-- Width-changing implicit conversion of an **unsigned** operand.
  `width` is the default-elaborated target width (envelope limitation —
  see module docstring). -/
  | resize (width : Nat) (arg : PExpr)
  /-- 4-state → 2-state squash (self-check-tier node; outside M0). -/
  | squash2 (width : Nat) (arg : PExpr)
  | sysCall (fn : SysFn) (arg : PExpr)
  /-- Semantic tier (phase 2): bit/element select `base[index]` — over a
  multi-dim packed base this reads one `elemW`-bit chunk (the element
  width comes from the declaration's dims at instantiation). -/
  | bitSel (base index : PExpr)
  /-- Semantic tier: constant-bound part select `base[msb:lsb]`. -/
  | partSel (base msb lsb : PExpr)
  /-- Semantic tier: replication `{count{arg}}` (count constant). -/
  | repl (count arg : PExpr)
  /-- Semantic tier: reduction `| & ^ ~| ~& ~^`. -/
  | reduce (op : RedOp) (arg : PExpr)
  /-- Semantic tier: `$signed`/`$unsigned` — width-preserving, bit
  identity; signedness acts through the consuming operator (the extractor
  spells signed comparisons `s<` …), so instantiation passes through. -/
  | cast (signed : Bool) (arg : PExpr)
  | unsupported (svKind : String) (text : String)
deriving Repr, BEq, Inhabited

/-- One packed dimension `[msb:lsb]` with symbolic bounds. -/
structure PDim where
  msb : PExpr
  lsb : PExpr
deriving Repr, BEq, Inhabited

/-- A declared type: symbolic packed dimensions, an (enum) type
reference, or an unrecoverable dimension list. `resolved?` fields are
defaults-elaborated **metadata** (cross-checks only, never the
contract). -/
inductive PType where
  /-- `[]` = scalar; multi-dim outermost first; total width = product. -/
  | packed (dims : List PDim) (resolved? : Option Nat)
  | typeRef (name : String) (pkg : Option String) (resolved? : Option Nat)
  | unrecoverable (resolved? : Option Nat)
deriving Repr, BEq, Inhabited

/-- A `parameter` declaration (the design family's binder). `resolved?`
is the defaults-elaborated value — metadata. `type?` is the declared
parameter type when the source gives one (`parameter bit FALL_THROUGH`,
`parameter int unsigned DEPTH`): its width is the parameter's
self-determined width in value positions (untyped parameters are 32-bit
ints, §6.20.2). -/
structure PParam where
  name : String
  default? : Option PExpr := none
  resolved? : Option Int := none
  type? : Option PType := none
deriving Repr, BEq, Inhabited

/-- A `localparam` (evaluated from the bound parameters at
instantiation, in declaration order). `type?` as on `PParam`. -/
structure PLocalParam where
  name : String
  expr : PExpr
  resolved? : Option Int := none
  type? : Option PType := none
deriving Repr, BEq, Inhabited

/-- An enum member value: an integer, or an x/z bits string (metadata
fidelity — x/z members cannot be used as constants). -/
inductive EnumVal where
  | int (v : Int)
  | bits (s : String)
deriving Repr, BEq, DecidableEq, Inhabited

structure PEnumMember where
  name : String
  value : EnumVal
deriving Repr, BEq, Inhabited

/-- A named enum type: base width (a `PType`, usually packed) and the
ordered member list (data, never folded away). -/
structure PEnumType where
  name : String
  pkg : Option String := none
  base : PType
  members : List PEnumMember
deriving Repr, BEq, Inhabited

/-- A port / variable / net declaration with a symbolic type. Ports come
first (port-list order), then module-body declarations — the M0 decl
order. -/
structure PDecl where
  name : String
  type : PType
  isInput : Bool := false
  isOutput : Bool := false
  isNet : Bool := false
  init : Option PExpr := none
deriving Repr, BEq, Inhabited

/-- Assignment targets of the semantic tier: whole signal, bit/element
select, or constant part select — always over a declared signal name (no
nested selects, no concat LHS: the CV32E40P provable files use neither). -/
inductive PLhs where
  | ident (name : String)
  | bitSel (name : String) (index : PExpr)
  | partSel (name : String) (msb lsb : PExpr)
deriving Repr, BEq, Inhabited

/-- The targeted signal's name. -/
def PLhs.name : PLhs → String
  | .ident n | .bitSel n _ | .partSel n _ _ => n

/-- Statements: the M0 shapes over `PExpr` (identifier targets), plus the
semantic tier's select-target assignments (`…L`) and `case` (plain /
`unique` / `inside` — §12.5.4). `caseStmt.items` are `(patterns, body)`
pairs in source order; a comma list is ONE item with several patterns. -/
inductive PStmt where
  | blockingAssign (target : String) (value : PExpr)
  | nbaAssign (target : String) (value : PExpr)
  | ifStmt (cond : PExpr) (thenBranch : PStmt) (elseBranch : Option PStmt)
  | block (body : List PStmt)
  | blockingAssignL (target : PLhs) (value : PExpr)
  | nbaAssignL (target : PLhs) (value : PExpr)
  | caseStmt (subject : PExpr) (items : List (List PExpr × PStmt))
      (default? : Option PStmt) (inside : Bool) (check : CaseCheck)
  | unsupported (svKind : String) (text : String)
deriving Repr, BEq, Inhabited

/-- Processes: M0 shapes plus select-target continuous assigns and the
async active-low reset event list (`@(posedge clock or negedge rstn)`). -/
inductive PProcess where
  | alwaysFF (clock : String) (body : PStmt)
  | alwaysPlain (clock : String) (body : PStmt)
  | alwaysComb (body : PStmt)
  | assign (target : String) (value : PExpr)
  | assignL (target : PLhs) (value : PExpr)
  | alwaysFFR (clock rstn : String) (body : PStmt)
  | unsupported (svKind : String) (text : String)
deriving Repr, BEq, Inhabited

/-- Generate items. `genFor` is ONE structural node — genvar, symbolic
`init`/`bound`/`step`, body **template** (never unrolled in the data);
`genIf` keeps its symbolic condition (`elseB = []` when there is no else
branch; else-if chains are an `elseB` containing one `genIf`).
`resolvedCount?` is defaults-elaborated metadata. -/
inductive GenItem where
  | process (p : PProcess)
  | genFor (label : Option String) (genvar : String) (init bound step : PExpr)
      (resolvedCount? : Option Nat) (body : List GenItem)
  | genIf (cond : PExpr) (thenB elseB : List GenItem)
  | unsupported (svKind : String) (text : String)
deriving Repr, BEq, Inhabited

/-- A parametric design — the sv-0.2 module payload. `params` order is
the **binder order** of the design family. `others` are out-of-tier
module members (kept as loud unsupported processes at instantiation). -/
structure PDesign where
  name : String
  params : List PParam
  localParams : List PLocalParam
  enums : List PEnumType
  decls : List PDecl
  processes : List PProcess
  generates : List GenItem
  others : List (String × String) := []
deriving Repr, BEq, Inhabited

/-! ## The instantiation environment -/

/-- Instantiation environment: bound integer constants (parameters,
localparams, in-scope genvars — first match wins, so genvar bindings
shadow), instantiated declaration widths, and the enum tables. -/
structure IEnv where
  vals : List (String × Int) := []
  widths : List (String × Nat) := []
  enums : List (String × Nat) := []
  members : List ((String × String) × LVec) := []
  /-- Declared widths of TYPED parameters/localparams (semantic tier;
  untyped parameters are 32-bit ints and are absent here). -/
  pwidths : List (String × Nat) := []
deriving Repr, Inhabited

/-- Bind a constant (prepend — shadows outer bindings of the name). -/
def IEnv.bindVal (env : IEnv) (n : String) (v : Int) : IEnv :=
  { env with vals := (n, v) :: env.vals }

/-! ## Constant tier: `evalInt` -/

private def b2i (b : Bool) : Int := if b then 1 else 0

/-- Evaluate a symbolic expression as an integer constant (parameter
defaults, localparams, generate headers/conditions, dimension bounds,
system calls). Loud `.error` on anything value-tier or unbound — see the
module docstring for the operator semantics ledger. -/
def evalInt (env : IEnv) : PExpr → Except String Int
  | .int v => .ok v
  | .lit v =>
      match v.toNat? with
      | some n => .ok (n : Int)
      | none => .error "x/z literal in a constant context"
  | .ident n => .error s!"signal '{n}' in a constant context"
  | .paramRef n none =>
      match env.vals.lookup n with
      | some v => .ok v
      | none => .error s!"unbound parameter '{n}'"
  | .paramRef n (some p) => .error s!"package-scoped parameter '{p}::{n}'"
  | .genvarRef n =>
      match env.vals.lookup n with
      | some v => .ok v
      | none => .error s!"genvar '{n}' outside its loop"
  | .enumRef ty mem _ =>
      match env.members.lookup (ty, mem) with
      | some v =>
          match v.toNat? with
          | some n => .ok (n : Int)
          | none => .error s!"enum member {ty}::{mem} has x/z bits"
      | none => .error s!"unknown enum member {ty}::{mem}"
  | .fill _ => .error "unbased-unsized literal in a constant context (no context width)"
  | .unary op a => do
      let v ← evalInt env a
      match op with
      | .m0 .neg => .ok (-v)
      | .m0 .lnot => .ok (b2i (v == 0))
      | .m0 .bnot => .error "'~' in a constant context (width-dependent)"
      | .plus => .ok v
      | .inc | .dec => .error "'++'/'--' outside a generate step"
  | .binary op l r => do
      let a ← evalInt env l
      let b ← evalInt env r
      match op with
      | .m0 .add => .ok (a + b)
      | .m0 .sub => .ok (a - b)
      | .m0 .and | .m0 .or | .m0 .xor =>
          if a < 0 || b < 0 then
            .error "bitwise operator on a negative constant (width-dependent)"
          else
            let x := a.toNat
            let y := b.toNat
            .ok (Int.ofNat (match op with
              | .m0 .and => x &&& y
              | .m0 .or => x ||| y
              | _ => x ^^^ y))
      | .m0 .eq => .ok (b2i (a == b))
      | .m0 .ne => .ok (b2i (a != b))
      | .m0 .lt | .slt => .ok (b2i (decide (a < b)))
      | .m0 .le | .sle => .ok (b2i (decide (a ≤ b)))
      | .m0 .gt | .sgt => .ok (b2i (decide (a > b)))
      | .m0 .ge | .sge => .ok (b2i (decide (a ≥ b)))
      | .ceq => .ok (b2i (a == b))
      | .cne => .ok (b2i (a != b))
      | .land => .ok (b2i (a != 0 && b != 0))
      | .lor => .ok (b2i (a != 0 || b != 0))
      | .mul => .ok (a * b)
      | .div => if b == 0 then .error "division by zero" else .ok (a.tdiv b)
      | .mod => if b == 0 then .error "modulo by zero" else .ok (a.tmod b)
      | .pow =>
          if b < 0 then .error "'**' with a negative exponent" else .ok (a ^ b.toNat)
      | .shl | .ashl =>
          if b < 0 then .error "shift by a negative amount" else .ok (a * (2 : Int) ^ b.toNat)
      | .shr =>
          if a < 0 then .error "'>>' of a negative constant (width-dependent)"
          else if b < 0 then .error "shift by a negative amount"
          else .ok (a.tdiv ((2 : Int) ^ b.toNat))
      | .ashr =>
          if b < 0 then .error "shift by a negative amount"
          else .ok (a.fdiv ((2 : Int) ^ b.toNat))
  | .ternary c t e => do
      let cv ← evalInt env c
      if cv != 0 then evalInt env t else evalInt env e
  | .concat _ => .error "concatenation in a constant context"
  | .resize w a => do
      let v ← evalInt env a
      .ok (v.emod ((2 : Int) ^ w))
  | .squash2 _ a => evalInt env a
  | .sysCall fn a =>
      match fn, a with
      | .clog2, e => do
          let v ← evalInt env e
          if v < 0 then .error "$clog2 of a negative value" else .ok (clog2 v.toNat : Int)
      | .bits, .ident n | .size, .ident n =>
          match env.widths.lookup n with
          | some w => .ok (w : Int)
          | none => .error s!"$bits/$size of undeclared signal '{n}'"
      | .high, .ident n =>
          match env.widths.lookup n with
          | some (w + 1) => .ok (w : Int)
          | some 0 => .error s!"$high of width-0 signal '{n}'"
          | none => .error s!"$high of undeclared signal '{n}'"
      | f, _ => .error s!"{f.sym} argument outside the declared-signal tier"
  | .bitSel base idx => do
      let v ← evalInt env base
      let i ← evalInt env idx
      if v < 0 then .error "bit select of a negative constant (width-dependent)"
      else if i < 0 then .error "negative bit-select index"
      else .ok (Int.ofNat ((v.toNat >>> i.toNat) % 2))
  | .partSel base msb lsb => do
      let v ← evalInt env base
      let m ← evalInt env msb
      let l ← evalInt env lsb
      if v < 0 then .error "part select of a negative constant (width-dependent)"
      else if l < 0 || m < l then .error "bad part-select bounds"
      else .ok (Int.ofNat ((v.toNat >>> l.toNat) % 2 ^ (m - l + 1).toNat))
  | .repl _ _ => .error "replication in a constant context"
  | .reduce _ _ => .error "reduction in a constant context (width-dependent)"
  | .cast _ a => evalInt env a
  | .unsupported k _ => .error s!"unsupported node '{k}' in a constant context"

/-! ## Widths -/

/-- Width of one packed dimension: `|msb - lsb| + 1`. -/
def PDim.width (env : IEnv) (d : PDim) : Except String Nat := do
  let m ← evalInt env d.msb
  let l ← evalInt env d.lsb
  .ok ((m - l).natAbs + 1)

private def dimsWidth (env : IEnv) : List PDim → Except String Nat
  | [] => .ok 1
  | d :: rest => do
      let w ← d.width env
      let ws ← dimsWidth env rest
      .ok (w * ws)

/-- Instantiated bit width of a declared type (multi-dim packed = product
— a packed array is one bit vector at M0 level). -/
def PType.width (env : IEnv) : PType → Except String Nat
  | .packed dims _ => dimsWidth env dims
  | .typeRef n _ _ =>
      match env.enums.lookup n with
      | some w => .ok w
      | none => .error s!"unknown type '{n}'"
  | .unrecoverable _ => .error "unrecoverable packed dimensions"

/-! ## Value tier: self-determined widths and `instExpr` -/

private def maxW : Option Nat → Option Nat → Option Nat
  | some a, some b => some (max a b)
  | some a, none => some a
  | none, some b => some b
  | none, none => none

mutual
/-- Self-determined width of a value-position expression (LRM §11.6
restricted to this vocabulary), under the instantiated declaration
widths. `none` = context-determined or unknowable. -/
def selfWidth (env : IEnv) : PExpr → Option Nat
  | .lit v => some v.width
  | .ident n => env.widths.lookup n
  | .paramRef .. | .genvarRef _ | .int _ | .sysCall .. => some 32
  | .enumRef ty _ _ => env.enums.lookup ty
  | .fill _ => none
  | .unary op a =>
      match op with
      | .m0 .lnot => some 1
      | .m0 _ | .plus => selfWidth env a
      | .inc | .dec => none
  | .binary op l r =>
      match op with
      | .m0 .eq | .m0 .ne | .m0 .lt | .m0 .le | .m0 .gt | .m0 .ge
      | .slt | .sle | .sgt | .sge | .ceq | .cne | .land | .lor => some 1
      | .shl | .shr | .ashl | .ashr | .pow => selfWidth env l
      | _ => maxW (selfWidth env l) (selfWidth env r)
  | .ternary _ t e => maxW (selfWidth env t) (selfWidth env e)
  | .concat parts => selfWidthSum env parts
  | .resize w _ => some w
  | .squash2 w _ => some w
  -- Semantic-tier nodes: the M0 layer does not know element widths
  -- (`Param2.lean`'s `selfWidth2` does); `none` = unknowable here.
  | .bitSel .. | .partSel .. | .repl .. => none
  | .reduce .. => some 1
  | .cast _ a => selfWidth env a
  | .unsupported .. => none

def selfWidthSum (env : IEnv) : List PExpr → Option Nat
  | [] => some 0
  | p :: rest =>
      match selfWidth env p, selfWidthSum env rest with
      | some a, some b => some (a + b)
      | _, _ => none
end

/-- An integer constant materialized at the context width (32 — the SV
int width — when no context width is known). -/
private def intLit (ctx : Option Nat) (v : Int) : Expr :=
  .lit (LVec.ofInt (ctx.getD 32) v)

mutual
/-- Instantiate a value-position expression to an M0 `Expr` under context
width `ctx` (the module docstring's ledger). Total: every failure is a
loud `Expr.unsupported`, reached-sensitive exactly like extractor-emitted
ones. -/
def instExpr (env : IEnv) (ctx : Option Nat) : PExpr → Expr
  | .lit v => .lit v
  | .ident n => .ident n
  | .int v => intLit ctx v
  | .fill b =>
      match ctx with
      | some w => .lit (LVec.replicate w b)
      | none => .unsupported "Fill:width" "no context width for unbased-unsized literal"
  | .paramRef n none =>
      match env.vals.lookup n with
      | some v => intLit ctx v
      | none => .unsupported "ParamRef:unbound" n
  | .paramRef n (some p) => .unsupported "ParamRef:package" s!"{p}::{n}"
  | .genvarRef n =>
      match env.vals.lookup n with
      | some v => intLit ctx v
      | none => .unsupported "GenvarRef:unbound" n
  | .enumRef ty mem _ =>
      match env.members.lookup (ty, mem) with
      | some v => .lit v
      | none => .unsupported "EnumRef:unknown" s!"{ty}::{mem}"
  | .unary op a =>
      match op with
      | .m0 .lnot => .unary .lnot (instExpr env none a)
      | .m0 uop => .unary uop (instExpr env (maxW ctx (selfWidth env a)) a)
      | .plus => instExpr env ctx a
      | .inc | .dec => .unsupported "UnaryExpression:incdec" ""
  | .binary op l r =>
      match op with
      | .m0 .add | .m0 .sub | .m0 .and | .m0 .or | .m0 .xor =>
          let octx := match ctx with
            | some w => some w
            | none => maxW (selfWidth env l) (selfWidth env r)
          .binary (match op with
              | .m0 bop => bop
              | _ => .add)  -- unreachable: this arm only matches `.m0`
            (instExpr env octx l) (instExpr env octx r)
      | .m0 .eq | .m0 .ne | .m0 .lt | .m0 .le | .m0 .gt | .m0 .ge =>
          let octx := maxW (selfWidth env l) (selfWidth env r)
          .binary (match op with
              | .m0 bop => bop
              | _ => .eq)  -- unreachable
            (instExpr env octx l) (instExpr env octx r)
      | _ =>
          match evalInt env (.binary op l r) with
          | .ok v => intLit ctx v
          | .error e => .unsupported s!"BinaryExpression:{op.sym}" e
  | .ternary c t e =>
      let actx := match ctx with
        | some w => some w
        | none => maxW (selfWidth env t) (selfWidth env e)
      .ternary (instExpr env none c) (instExpr env actx t) (instExpr env actx e)
  | .concat parts => .concat (instParts env parts).toArray
  | .resize w a =>
      if ctx.getD w != w then
        .unsupported "Resize:context"
          s!"default-elaborated resize width {w} vs context width {ctx.getD w}"
      else
        match selfWidth env a with
        | none => .unsupported "Resize:width" "operand width unknown"
        | some ow =>
            if ow == w then instExpr env (some w) a
            else if ow < w then
              .concat #[.lit (LVec.replicate (w - ow) .l0), instExpr env (some ow) a]
            else .unsupported "Resize:truncate" s!"{ow} -> {w}"
  | .squash2 .. => .unsupported "Squash2" "2-state squash outside the M0 value core"
  | .sysCall fn a =>
      match evalInt env (.sysCall fn a) with
      | .ok v => intLit ctx v
      | .error e => .unsupported "SysCall" e
  -- Semantic-tier nodes stay loud on the M0 path (they lower in
  -- `Param2.lean`'s `instantiate2` → `Design2`).
  | .bitSel .. => .unsupported "T2:BitSel" "select outside the M0 tier"
  | .partSel .. => .unsupported "T2:PartSel" "select outside the M0 tier"
  | .repl .. => .unsupported "T2:Repl" "replication outside the M0 tier"
  | .reduce .. => .unsupported "T2:Reduce" "reduction outside the M0 tier"
  | .cast .. => .unsupported "T2:Cast" "cast outside the M0 tier"
  | .unsupported k t => .unsupported k t

/-- Concat parts: each part is self-determined (an inner fill with no
self width is loud — the LRM agrees: unsized literals are illegal in
concats). -/
def instParts (env : IEnv) : List PExpr → List Expr
  | [] => []
  | p :: rest => instExpr env (selfWidth env p) p :: instParts env rest
end

/-! ## Statements, processes, declarations -/

mutual
/-- Instantiate a statement (assign targets take their declared widths as
context). -/
def instStmt (env : IEnv) : PStmt → Stmt
  | .blockingAssign t v => .blockingAssign t (instExpr env (env.widths.lookup t) v)
  | .nbaAssign t v => .nbaAssign t (instExpr env (env.widths.lookup t) v)
  | .ifStmt c th el =>
      .ifStmt (instExpr env none c) (instStmt env th)
        (match el with
         | some s => some (instStmt env s)
         | none => none)
  | .block body => .block (instStmts env body).toArray
  | .blockingAssignL .. => .unsupported "T2:AssignL" "select target outside the M0 tier"
  | .nbaAssignL .. => .unsupported "T2:AssignL" "select target outside the M0 tier"
  | .caseStmt .. => .unsupported "T2:Case" "case statement outside the M0 tier"
  | .unsupported k t => .unsupported k t

def instStmts (env : IEnv) : List PStmt → List Stmt
  | [] => []
  | s :: rest => instStmt env s :: instStmts env rest
end

/-- Instantiate a process. -/
def instProcess (env : IEnv) : PProcess → Process
  | .alwaysFF c b => .alwaysFF c (instStmt env b)
  | .alwaysPlain c b => .alwaysPlain c (instStmt env b)
  | .alwaysComb b => .alwaysComb (instStmt env b)
  | .assign t v => .assign t (instExpr env (env.widths.lookup t) v)
  | .assignL .. => .unsupported "T2:AssignL" "select target outside the M0 tier"
  | .alwaysFFR .. => .unsupported "T2:AlwaysFFR" "async reset outside the M0 tier"
  | .unsupported k t => .unsupported k t

/-- Instantiate one declaration (earlier declarations' widths already in
`env` — `$bits`/`$high` may look back, never forward). A non-literal
initializer is outside the M0 ingestion tier (loud). -/
def instDecl (env : IEnv) (pd : PDecl) : Res Decl :=
  match pd.type.width env with
  | .error e => .unsupported s!"decl '{pd.name}': {e}"
  | .ok w =>
      match pd.init with
      | none =>
          .ok { name := pd.name, width := w, isInput := pd.isInput, isOutput := pd.isOutput }
      | some ie =>
          match instExpr env (some w) ie with
          | .lit v =>
              .ok { name := pd.name, width := w, isInput := pd.isInput,
                    isOutput := pd.isOutput, init := some v }
          | _ =>
              .unsupported s!"decl '{pd.name}': non-literal initializer outside the M0 tier"

/-- Instantiate the declarations in order, threading each new width into
the environment. -/
def buildDecls (env : IEnv) : List PDecl → Res (List Decl)
  | [] => .ok []
  | pd :: rest => do
      let dc ← instDecl env pd
      let ds ← buildDecls { env with widths := (pd.name, dc.width) :: env.widths } rest
      .ok (dc :: ds)

/-- Bind localparams in declaration order (each sees the parameters and
all earlier localparams). -/
def bindLocals (env : IEnv) : List PLocalParam → Res IEnv
  | [] => .ok env
  | lp :: rest =>
      match evalInt env lp.expr with
      | .error e => .unsupported s!"localparam '{lp.name}': {e}"
      | .ok v => bindLocals (env.bindVal lp.name v) rest

private def enumMemberVals (ty : String) (w : Nat) :
    List PEnumMember → Res (List ((String × String) × LVec))
  | [] => .ok []
  | m :: rest => do
      let v ← match m.value with
        | .int v => pure (LVec.ofInt w v)
        | .bits s =>
            match LVec.ofBinLit? w s with
            | some v => pure v
            | none => Res.unsupported s!"enum member {ty}::{m.name}: bad bits {s.quote}"
      let vs ← enumMemberVals ty w rest
      .ok (((ty, m.name), v) :: vs)

/-- Bind the enum tables (base widths may mention parameters). -/
def bindEnums (env : IEnv) : List PEnumType → Res IEnv
  | [] => .ok env
  | et :: rest =>
      match et.base.width env with
      | .error e => .unsupported s!"enum '{et.name}': {e}"
      | .ok w => do
          let ms ← enumMemberVals et.name w et.members
          bindEnums { env with enums := (et.name, w) :: env.enums,
                               members := ms ++ env.members } rest

/-! ## Generate expansion -/

/-- Decode a generate step: `g++` ↦ `+1`, `g--` ↦ `-1` (the extractor's
committed step vocabulary). -/
def stepDelta (g : String) : PExpr → Except String Int
  | .unary .inc (.genvarRef g') =>
      if g' == g then .ok 1 else .error s!"step increments '{g'}', loop genvar is '{g}'"
  | .unary .dec (.genvarRef g') =>
      if g' == g then .ok (-1) else .error s!"step decrements '{g'}', loop genvar is '{g}'"
  | _ => .error "generate step outside the ++/-- tier"

/-- The genvar value sequence of a generate-for: from `i`, keep values
while `bound` evaluates nonzero, stepping by `δ`. Fueled — the one
genuinely unbounded recursion of instantiation (`.timeout` = fuel
exhausted; loop bounds beyond the surface fuel are loud, never wrong). -/
def genvarSeq (env : IEnv) (g : String) (bound : PExpr) (δ : Int) :
    Nat → Int → Res (List Int)
  | 0, _ => .timeout
  | fuel + 1, i =>
      match evalInt (env.bindVal g i) bound with
      | .error e => .unsupported s!"generate bound: {e}"
      | .ok v =>
          if v == 0 then .ok []
          else do
            let rest ← genvarSeq env g bound δ fuel (i + δ)
            .ok (i :: rest)

mutual
/-- Expand one generate item into M0 processes. Generate-local
declarations are outside this slice (they need per-instance scoping) —
they arrive as loud unsupported items from the parser. -/
def GenItem.expand (env : IEnv) (iterFuel : Nat) : GenItem → Res (List Process)
  | .process p => .ok [instProcess env p]
  | .unsupported k t => .ok [.unsupported k t]
  | .genIf cond thenB elseB =>
      match evalInt env cond with
      | .error e => .unsupported s!"generate if: {e}"
      | .ok v =>
          if v != 0 then expandList env iterFuel thenB
          else expandList env iterFuel elseB
  | .genFor _label g initE bound step _rc body =>
      match evalInt env initE, stepDelta g step with
      | .ok i0, .ok δ => do
          let vs ← genvarSeq env g bound δ iterFuel i0
          expandIters env iterFuel g vs body
      | .error e, _ => .unsupported s!"generate for: {e}"
      | _, .error e => .unsupported s!"generate for: {e}"
  termination_by it => (sizeOf it, 0)
  decreasing_by all_goals (simp_wf; omega)

/-- Expand a generate item list (concatenation, source order). -/
def expandList (env : IEnv) (iterFuel : Nat) : List GenItem → Res (List Process)
  | [] => .ok []
  | it :: rest => do
      let ps ← it.expand env iterFuel
      let qs ← expandList env iterFuel rest
      .ok (ps ++ qs)
  termination_by l => (sizeOf l, 0)
  decreasing_by all_goals (simp_wf; omega)

/-- Expand a generate-for body template at each genvar value —
**the** family recursion (`expandIters_*` lemmas below are its
induction handles). -/
def expandIters (env : IEnv) (iterFuel : Nat) (g : String) :
    List Int → List GenItem → Res (List Process)
  | [], _ => .ok []
  | v :: vs, body => do
      let ps ← expandList (env.bindVal g v) iterFuel body
      let qs ← expandIters env iterFuel g vs body
      .ok (ps ++ qs)
  termination_by vs body => (sizeOf body, vs.length + 1)
  decreasing_by all_goals (simp_wf; omega)
end

/-! ## `instantiate` -/

/-- The loud error design: any run of it is `.unsupported` at the first
cycle (`Process.unsupported` is comb-phase — the M0 loudness discipline),
and `Design.hasUnsupported` is `true`. -/
def Design.errorDesign (name msg : String) : Design :=
  { name, decls := #[], processes := #[.unsupported "Instantiate" msg] }

/-- **Instantiate a parametric design at concrete parameter values**
(`args` in declaration order — the binder encoding of
`load_design_sv2`). Substitutes parameters, evaluates localparams/enum
tables/declared widths in order, instantiates every process, and expands
the generate items (`iterFuel` bounds each generate loop's iteration
count). Errors are loud: `.unsupported` on bad parameters (arity,
failing constant evaluation), `.timeout` on generate fuel exhaustion.
Out-of-M0-tier *constructs* do NOT fail instantiation — they become
`.unsupported` nodes inside the design, loud only when the M0 interpreter
reaches them. -/
def PDesign.instantiate (d : PDesign) (args : List Int) (iterFuel : Nat := 4096) :
    Res Design :=
  if args.length != d.params.length then
    .unsupported s!"parameter arity: got {args.length}, want {d.params.length}"
  else do
    let env0 : IEnv := { vals := (d.params.map (·.name)).zip args }
    let env1 ← bindLocals env0 d.localParams
    let env2 ← bindEnums env1 d.enums
    let decls ← buildDecls env2 d.decls
    let envP := { env2 with widths := decls.map fun dc => (dc.name, dc.width) }
    let gens ← expandList envP iterFuel d.generates
    .ok { name := d.name
          decls := decls.toArray
          processes :=
            ((d.processes.map (instProcess envP)) ++ gens
              ++ d.others.map fun (k, t) => Process.unsupported k t).toArray }

/-- Surface iteration fuel: covers every generate loop whose iteration
count is at most quadratic in the total parameter magnitude (in
particular the `2^(clog2 W)`-shaped tree loops of `ff_one`). A loop
beyond it instantiates to the loud timeout design — never wrong,
possibly conservative. -/
def PDesign.surfaceFuel (args : List Int) : Nat :=
  let s := (args.map Int.natAbs).sum
  (s + 2) * (s + 2) + 64

/-- The `Design`-valued instantiation used by the `load_design_sv2`
binder encoding (`name : (params : Nat…) → Design`): errors collapse to
the loud `errorDesign` (any run is `.unsupported`), so the family is
total without ever being silently wrong. Proof work should prefer
`instantiate` (the `Res` form) and the lemmas below. -/
def PDesign.instantiateD (d : PDesign) (args : List Int) : Design :=
  match d.instantiate args (PDesign.surfaceFuel args) with
  | .ok m => m
  | .timeout => .errorDesign d.name "generate expansion fuel exhausted"
  | .unsupported msg => .errorDesign d.name msg

/-! ## Defaults and the metadata cross-check

The envelope's `resolved`-family fields are slang's own
defaults-elaboration — metadata, never the contract. `crossCheck`
replays our elaboration at the defaults and compares: a nonempty result
means the Lean elaboration semantics and slang disagree, and the
`load_design_sv2` command refuses the envelope (the ingestion-time
differential test against the frontend). -/

/-- Evaluate the parameter defaults in declaration order (each sees the
earlier ones). -/
def PDesign.defaultArgs (d : PDesign) : Res (List Int) :=
  go {} d.params
where
  go (env : IEnv) : List PParam → Res (List Int)
    | [] => .ok []
    | p :: rest =>
        match p.default? with
        | none => .unsupported s!"parameter '{p.name}' has no default"
        | some e =>
            match evalInt env e with
            | .error err => .unsupported s!"parameter '{p.name}' default: {err}"
            | .ok v => do
                let vs ← go (env.bindVal p.name v) rest
                .ok (v :: vs)

private def checkLocals (env : IEnv) : List PLocalParam → List String × IEnv
  | [] => ([], env)
  | lp :: rest =>
      match evalInt env lp.expr with
      | .error e => ([s!"localparam '{lp.name}': {e}"], env)
      | .ok v =>
          let tail := checkLocals (env.bindVal lp.name v) rest
          (match lp.resolved? with
            | some r =>
                if r == v then tail.1
                else s!"localparam '{lp.name}': ours {v} ≠ resolved {r}" :: tail.1
            | none => tail.1, tail.2)

private def PType.resolved? : PType → Option Nat
  | .packed _ r => r
  | .typeRef _ _ r => r
  | .unrecoverable r => r

private def checkDecls (env : IEnv) : List PDecl → List String
  | [] => []
  | pd :: rest =>
      match instDecl env pd with
      | .ok dc =>
          let tail := checkDecls
            { env with widths := (pd.name, dc.width) :: env.widths } rest
          match pd.type.resolved? with
          | some r =>
              if r == dc.width then tail
              else s!"decl '{pd.name}': our width {dc.width} ≠ resolved {r}" :: tail
          | none => tail
      | .timeout => [s!"decl '{pd.name}': timeout"]
      | .unsupported e => [e]

private def checkGenerates (env : IEnv) (iterFuel : Nat) : List GenItem → List String
  | [] => []
  | .genFor label g initE bound step rc? _body :: rest =>
      let name := label.getD g
      let here :=
        match evalInt env initE, stepDelta g step with
        | .ok i0, .ok δ =>
            match genvarSeq env g bound δ iterFuel i0, rc? with
            | .ok vs, some rc =>
                if vs.length == rc then []
                else [s!"generate '{name}': our count {vs.length} ≠ resolved {rc}"]
            | .ok _, none => []
            | .timeout, _ => [s!"generate '{name}': iteration fuel exhausted"]
            | .unsupported e, _ => [s!"generate '{name}': {e}"]
        | .error e, _ | _, .error e => [s!"generate '{name}': {e}"]
      here ++ checkGenerates env iterFuel rest
  | _ :: rest => checkGenerates env iterFuel rest

/-- Replay the defaults elaboration and compare against every `resolved`
metadata field the envelope carries: parameter defaults, localparams,
declared widths, and **top-level** generate-for counts (nested counts
are defaults-dependent per instance; the top level is what slang's
`resolved_count` reports for these envelopes). `[]` = clean. -/
def PDesign.crossCheck (d : PDesign) : List String :=
  match d.defaultArgs with
  | .timeout => ["defaults: timeout"]
  | .unsupported e => [s!"defaults: {e}"]
  | .ok args =>
      let paramMsgs := (d.params.zip args).filterMap fun (p, v) =>
        match p.resolved? with
        | some r => if r == v then none else some s!"parameter '{p.name}': ours {v} ≠ resolved {r}"
        | none => none
      let env0 : IEnv := { vals := (d.params.map (·.name)).zip args }
      let (localMsgs, env1) := checkLocals env0 d.localParams
      match bindEnums env1 d.enums with
      | .ok env2 =>
          paramMsgs ++ localMsgs ++ checkDecls env2 d.decls
            ++ checkGenerates
                { env2 with widths := declWidths env2 d.decls } (PDesign.surfaceFuel args)
                d.generates
      | .timeout => paramMsgs ++ localMsgs ++ ["enums: timeout"]
      | .unsupported e => paramMsgs ++ localMsgs ++ [s!"enums: {e}"]
where
  declWidths (env : IEnv) (decls : List PDecl) : List (String × Nat) :=
    match buildDecls env decls with
    | .ok ds => ds.map fun dc => (dc.name, dc.width)
    | _ => []

/-- How many metadata fields `crossCheck` can actually COMPARE.

**Why this exists.** `crossCheck` skips every field whose `resolved?`
metadata is absent — the `| none =>` arms in the parameter fold, in
`checkLocals`, in `checkDecls`, and the count-less `genFor` — and returns
`[]`. So `[]` means BOTH "everything agreed" and "nothing was compared",
and an envelope carrying no `resolved` metadata at all passed the
"ingestion-time differential test against the frontend" without a single
comparison being made (quality audit 2026-08-23, `sv` MEDIUM,
`Param.lean:997`).

That is the same defect the family's `live` flag fixes for verdict rows:
**a vacuous run must not serialize as agreement.** Counting the
*comparable* fields is exact rather than approximate here, because
`crossCheck` compares precisely the fields whose metadata is `some` —
this count and the number of comparisons performed are the same number. -/
private def comparableCount (d : PDesign) : Nat :=
  (d.params.filter (·.resolved?.isSome)).length
  + (d.localParams.filter (·.resolved?.isSome)).length
  + (d.decls.filter (fun pd => (PType.resolved? pd.type).isSome)).length
  + (d.generates.filter (fun g =>
        match g with
        | .genFor _ _ _ _ _ rc _ => rc.isSome
        | _ => false)).length

/-- `crossCheck`'s messages PAIRED WITH the number of comparisons made, so
that "clean" and "compared nothing" stop being the same value.

`crossCheck` itself is unchanged and still returns just the messages, so
every existing `#guard … == []` keeps its meaning; the loader
(`load_design_sv2`) is what consumes the count and refuses **VACUOUS**. -/
def PDesign.crossCheckFull (d : PDesign) : List String × Nat :=
  (d.crossCheck, comparableCount d)

/-! ## Starter lemmas 1: instantiation preserves the declaration surface

Specs are ports-only, so the load-bearing well-formedness fact is that
`instantiate` never invents, drops, reorders, or re-flags declarations —
the name/direction surface of the instantiated design is
**parameter-independent** data of the `PDesign`. -/

/-- The parameter-independent declaration surface: names and port
directions, in declaration order. -/
def PDesign.declSig (d : PDesign) : List (String × Bool × Bool) :=
  d.decls.map fun pd => (pd.name, pd.isInput, pd.isOutput)

/-- Names of a `PDesign`'s declarations (ports first, declaration
order). -/
def PDesign.declNames (d : PDesign) : List String := d.decls.map (·.name)

/-- Name well-formedness of a parametric design: declared names are
distinct. -/
def PDesign.WFNames (d : PDesign) : Prop := d.declNames.Nodup

/-- Name well-formedness of an M0 design (what `SvState.set`/`lookup`
determinism arguments want). -/
def Design.WFNames (m : Design) : Prop := (m.decls.toList.map (·.name)).Nodup

instance (d : PDesign) : Decidable d.WFNames :=
  inferInstanceAs (Decidable d.declNames.Nodup)

instance (m : Design) : Decidable m.WFNames :=
  inferInstanceAs (Decidable (m.decls.toList.map (·.name)).Nodup)

theorem instDecl_sig {env : IEnv} {pd : PDecl} {dc : Decl}
    (h : instDecl env pd = .ok dc) :
    dc.name = pd.name ∧ dc.isInput = pd.isInput ∧ dc.isOutput = pd.isOutput := by
  unfold instDecl at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · cases h; exact ⟨rfl, rfl, rfl⟩
    · split at h
      · cases h; exact ⟨rfl, rfl, rfl⟩
      · exact absurd h (by simp)

theorem buildDecls_sig {l : List PDecl} :
    ∀ {env : IEnv} {r : List Decl}, buildDecls env l = .ok r →
      r.map (fun dc => (dc.name, dc.isInput, dc.isOutput)) =
        l.map (fun pd => (pd.name, pd.isInput, pd.isOutput)) := by
  induction l with
  | nil => intro env r h; cases h; rfl
  | cons pd rest ih =>
      intro env r h
      simp only [buildDecls, Res.bind_eq_ok] at h
      obtain ⟨dc, hdc, ds, hds, hr⟩ := h
      cases hr
      obtain ⟨hn, hi, ho⟩ := instDecl_sig hdc
      simp [hn, hi, ho, ih hds]

/-- **Instantiation preserves the declaration surface** — for every
parameter vector and fuel, the instantiated design's (name, input,
output) list is the `PDesign`'s `declSig`, i.e. the port surface is
parameter-independent. -/
theorem instantiate_declSig {d : PDesign} {args : List Int} {F : Nat} {m : Design}
    (h : d.instantiate args F = .ok m) :
    m.decls.toList.map (fun dc => (dc.name, dc.isInput, dc.isOutput)) = d.declSig := by
  unfold PDesign.instantiate at h
  split at h
  · exact absurd h (by simp)
  · simp only [Res.bind_eq_ok] at h
    obtain ⟨env1, _, env2, _, decls, hdecls, gens, _, hm⟩ := h
    cases hm
    simpa [PDesign.declSig] using buildDecls_sig hdecls

/-- The instantiated design's name is the source module name. -/
theorem instantiate_name {d : PDesign} {args : List Int} {F : Nat} {m : Design}
    (h : d.instantiate args F = .ok m) : m.name = d.name := by
  unfold PDesign.instantiate at h
  split at h
  · exact absurd h (by simp)
  · simp only [Res.bind_eq_ok] at h
    obtain ⟨_, _, _, _, _, _, _, _, hm⟩ := h
    cases hm; rfl

/-- Declared names are parameter-independent. -/
theorem instantiate_declNames {d : PDesign} {args : List Int} {F : Nat} {m : Design}
    (h : d.instantiate args F = .ok m) :
    m.decls.toList.map (·.name) = d.declNames := by
  have hs := instantiate_declSig h
  have h1 : (m.decls.toList.map (fun dc => (dc.name, dc.isInput, dc.isOutput))).map Prod.fst
      = d.declSig.map Prod.fst := by rw [hs]
  simpa [PDesign.declSig, PDesign.declNames, List.map_map, Function.comp_def] using h1

/-- **Instantiation preserves name well-formedness**: distinct declared
names in the parametric design give distinct declared names in every
instantiation. -/
theorem instantiate_WFNames {d : PDesign} {args : List Int} {F : Nat} {m : Design}
    (h : d.instantiate args F = .ok m) (hd : d.WFNames) : m.WFNames := by
  unfold Design.WFNames
  rw [instantiate_declNames h]
  exact hd

/-! ## Starter lemmas 2: generate expansion — the family induction handles -/

/-- `expandIters` **is** flatten-of-map: if each iteration's body
expansion is known, the whole family is their concatenation in genvar
order. Everything else about a `GenerateFor` family reduces through this
equation. -/
theorem expandIters_eq_flatten {env : IEnv} {F : Nat} {g : String}
    {body : List GenItem} {f : Int → List Process} :
    ∀ {vs : List Int},
      (∀ v ∈ vs, expandList (env.bindVal g v) F body = .ok (f v)) →
      expandIters env F g vs body = .ok (vs.map f).flatten := by
  intro vs
  induction vs with
  | nil => intro _; simp [expandIters]
  | cons v vs ih =>
      intro h
      have hv := h v (List.mem_cons_self ..)
      have hrest := ih fun w hw => h w (List.mem_cons_of_mem _ hw)
      simp [expandIters, hv, hrest]

/-- Membership in an expanded family: exactly the per-iteration
processes, for some genvar value of the loop. -/
theorem mem_expandIters {env : IEnv} {F : Nat} {g : String}
    {body : List GenItem} {f : Int → List Process} {vs : List Int} {ps : List Process}
    (hf : ∀ v ∈ vs, expandList (env.bindVal g v) F body = .ok (f v))
    (h : expandIters env F g vs body = .ok ps) (p : Process) :
    p ∈ ps ↔ ∃ v ∈ vs, p ∈ f v := by
  rw [expandIters_eq_flatten hf] at h
  cases h
  simp [List.mem_flatten, List.mem_map]
  constructor
  · rintro ⟨l, ⟨v, hv, rfl⟩, hp⟩; exact ⟨v, hv, hp⟩
  · rintro ⟨v, hv, hp⟩; exact ⟨f v, ⟨v, hv, rfl⟩, hp⟩

/-- Family size, uniform-template case: a body that expands to `c`
processes at every genvar value gives `c * |vs|` processes — the length
arithmetic of every `GenerateFor` family proof. -/
theorem expandIters_length_const {env : IEnv} {F : Nat} {g : String}
    {body : List GenItem} {f : Int → List Process} {c : Nat}
    {vs : List Int} {ps : List Process}
    (hf : ∀ v ∈ vs, expandList (env.bindVal g v) F body = .ok (f v))
    (hc : ∀ v ∈ vs, (f v).length = c)
    (h : expandIters env F g vs body = .ok ps) : ps.length = c * vs.length := by
  rw [expandIters_eq_flatten hf] at h
  cases h
  clear hf
  induction vs with
  | nil => simp
  | cons v vs ih =>
      have hi := ih fun w hw => hc w (List.mem_cons_of_mem _ hw)
      simp [List.flatten_cons, hc v (List.mem_cons_self ..), hi,
            Nat.mul_succ, Nat.add_comm]

/-- `[i0, i0+1, …, i0+n-1]` — the canonical ascending genvar value
sequence (the `List Int` counterpart of `List.range`, offset-friendly:
generate loops start anywhere). -/
def intRange (i0 : Int) : Nat → List Int
  | 0 => []
  | n + 1 => i0 :: intRange (i0 + 1) n

@[simp] theorem intRange_length : ∀ (n : Nat) (i0 : Int), (intRange i0 n).length = n
  | 0, _ => rfl
  | n + 1, i0 => by simp [intRange, intRange_length n]

@[simp] theorem mem_intRange {v : Int} :
    ∀ {n : Nat} {i0 : Int}, v ∈ intRange i0 n ↔ i0 ≤ v ∧ v < i0 + n := by
  intro n
  induction n with
  | zero => intro i0; simp [intRange]
  | succ n ih => intro i0; simp [intRange, ih]; omega

/-- A genvar reference under its own binding evaluates to the bound
value. -/
theorem evalInt_genvarRef_bind {env : IEnv} {g : String} {v : Int} :
    evalInt (env.bindVal g v) (.genvarRef g) = .ok v := by
  simp [evalInt, IEnv.bindVal]

/-- Signed `<` on evaluated operands (the canonical generate-loop
bound shape). -/
theorem evalInt_slt {env : IEnv} {l r : PExpr} {a b : Int}
    (hl : evalInt env l = .ok a) (hr : evalInt env r = .ok b) :
    evalInt env (.binary .slt l r) = .ok (b2i (decide (a < b))) := by
  simp only [evalInt, hl, hr]
  rfl

/-- The genvar sequence of the canonical ascending loop
(`for (g = i0; g s< e; g++)` with a loop-invariant bound expression
`e ⇓ N`): consecutive integers `i0, i0+1, …, N-1`, provided the fuel
exceeds the trip count. **The** induction workhorse for `ff_one`-shaped
∀-parameter families. -/
theorem genvarSeq_ascending {env : IEnv} {g : String} {e : PExpr} {N : Int}
    (he : ∀ i : Int, evalInt (env.bindVal g i) e = .ok N) :
    ∀ {fuel : Nat} (i0 : Int), (N - i0).toNat < fuel →
      genvarSeq env g (.binary .slt (.genvarRef g) e) 1 fuel i0 =
        .ok (intRange i0 (N - i0).toNat) := by
  intro fuel
  induction fuel with
  | zero => intro i0 h; omega
  | succ fuel ih =>
      intro i0 hfuel
      have hbound := evalInt_slt (evalInt_genvarRef_bind (env := env) (g := g) (v := i0)) (he i0)
      by_cases hlt : i0 < N
      · have hcount : (N - i0).toNat = (N - (i0 + 1)).toNat + 1 := by omega
        have hrec := ih (i0 + 1) (by omega)
        rw [hcount]
        simp [genvarSeq, hbound, hlt, b2i, hrec, intRange]
      · have hz : (N - i0).toNat = 0 := by omega
        rw [hz]
        simp [genvarSeq, hbound, hlt, b2i, intRange]

/-- Trip count of the canonical ascending loop. -/
theorem genvarSeq_ascending_length {env : IEnv} {g : String} {e : PExpr} {N : Int}
    (he : ∀ i : Int, evalInt (env.bindVal g i) e = .ok N)
    {fuel : Nat} {i0 : Int} (hfuel : (N - i0).toNat < fuel) {vs : List Int}
    (h : genvarSeq env g (.binary .slt (.genvarRef g) e) 1 fuel i0 = .ok vs) :
    vs.length = (N - i0).toNat := by
  rw [genvarSeq_ascending he i0 hfuel] at h
  cases h; simp

/-! ## Hand-built parametric smoke

`gen_sel(W, K)`: `W`-bit input `a`, output `y`; a generate-for over
`j s< K` whose body is a generate-if selecting exactly the last
iteration (`j == K-1`, via a localparam) to drive `assign y = a + j` —
exercising symbolic widths, localparam evaluation, `GenerateFor` +
`GenerateIf` expansion, and a genvar in a value position, all fully
inside the M0 tier after instantiation. -/

private def wm1 : PDim := ⟨.binary (.m0 .sub) (.paramRef "W" none) (.int 1), .int 0⟩

private def pGenSel : PDesign :=
  { name := "gen_sel"
    params := [
      { name := "W", default? := some (.int 8), resolved? := some 8 },
      { name := "K", default? := some (.int 3), resolved? := some 3 }]
    localParams := [
      { name := "KM1", expr := .binary (.m0 .sub) (.paramRef "K" none) (.int 1),
        resolved? := some 2 }]
    enums := []
    decls := [
      { name := "a", type := .packed [wm1] (some 8), isInput := true },
      { name := "y", type := .packed [wm1] (some 8), isOutput := true }]
    processes := []
    generates := [
      .genFor (some "gen") "j" (.int 0)
        (.binary .slt (.genvarRef "j") (.paramRef "K" none))
        (.unary .inc (.genvarRef "j")) (some 3)
        [.genIf (.binary (.m0 .eq) (.genvarRef "j") (.paramRef "KM1" none))
          [.process (.assign "y" (.binary (.m0 .add) (.ident "a") (.genvarRef "j")))]
          []]]
    others := [] }

-- Metadata cross-check at defaults is clean.
#guard pGenSel.crossCheck == []

-- Instantiation at the defaults: exactly one surviving assign, `y = a + 2#8`.
#guard pGenSel.instantiate [8, 3] ==
  .ok { name := "gen_sel"
        decls := #[
          { name := "a", width := 8, isInput := true },
          { name := "y", width := 8, isOutput := true }]
        processes := #[.assign "y" (.binary .add (.ident "a") (.lit (.ofNat 8 2)))] }

-- … and it RUNS under the untouched M0 cycle semantics: y = a + (K-1).
#guard (Res.toOption (run (pGenSel.instantiateD [8, 3]) σ_src 64 [[("a", LVec.ofNat 8 5)]])).map
        (fun tr => tr.map (fun st => SvState.showSignal st "y"))
      == some ["00000111"]

-- A different parameter point, same family: W = 4, K = 1 → y = a + 0.
#guard (Res.toOption (run (pGenSel.instantiateD [4, 1]) σ_src 64 [[("a", LVec.ofNat 4 9)]])).map
        (fun tr => tr.map (fun st => SvState.showSignal st "y"))
      == some ["1001"]

-- K = 0: empty family — y is undriven and stays x (still a legal run).
#guard (Res.toOption (run (pGenSel.instantiateD [4, 0]) σ_src 64 [[("a", LVec.ofNat 4 9)]])).map
        (fun tr => tr.map (fun st => SvState.showSignal st "y"))
      == some ["xxxx"]

-- Bad parameters are loud, not wrong.
#guard pGenSel.instantiate [8] == .unsupported "parameter arity: got 1, want 2"
#guard (pGenSel.instantiateD [8]).hasUnsupported
#guard run (pGenSel.instantiateD [8]) σ_src 64 [[]]
        == .unsupported "unsupported process 'Instantiate'"

-- The declaration surface is parameter-independent (executable instance
-- of `instantiate_declSig`).
#guard ((pGenSel.instantiate [4, 1]).toOption.map
          fun m => m.decls.toList.map (·.name)) == some ["a", "y"]

-- The ascending-loop lemma, demonstrated at a symbolic parameter: for
-- every K, the genvar sequence of `for (j = 0; j s< K; j++)` under
-- `K ↦ K` is `[0, …, K-1]`.
example (K : Nat) :
    genvarSeq { vals := [("K", (K : Int))] } "j"
        (.binary .slt (.genvarRef "j") (.paramRef "K" none)) 1 (K + 1) 0 =
      .ok (intRange 0 K) := by
  have he : ∀ i : Int,
      evalInt (IEnv.bindVal { vals := [("K", (K : Int))] } "j" i)
        (.paramRef "K" none) = .ok (K : Int) := by
    intro i
    simp [evalInt, IEnv.bindVal, List.lookup]
  have h := genvarSeq_ascending he (fuel := K + 1) 0 (by omega)
  simpa using h

end LeanModels.Sv
