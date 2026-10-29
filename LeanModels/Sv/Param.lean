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
  generate headers/conditions, dimension bounds, select labels. Two
  regimes, chosen per node by the syntactic INT class (`PExpr.isInt`):
  - **INT class** — unsized integers, genvars, system-call results, and
    parameters bound in `IEnv.vals` (untyped, or typed `int`/`integer`:
    32-bit signed), closed under `+ - * / % ** << >> <<< >>> & | ^`,
    unary `- +` and `?:`. Evaluated over **mathematical `Int`** (no
    32-bit wrap: no CV32E40P parameter comes near it — recorded
    restriction). `/` `%` truncate toward zero (`Int.tdiv`/`Int.tmod`,
    the SV rule), `**` requires a nonnegative exponent, `>>` requires a
    nonnegative operand (logical shift of a negative constant is
    width-dependent — loud error instead), `>>>` is arithmetic
    (`Int.fdiv`). Comparisons over two INT operands compare the
    mathematical values (32-bit signed on both sides).
  - **Everything else** — any operand that is a sized literal (unsigned
    at its own width), a parameter typed narrower than 32 bits or
    unsigned (bound in `IEnv.nvals` with its width and signedness), a
    `Resize`, a cast, a comparison result (1-bit unsigned), a constant
    select — goes to `evalSized`, the IEEE 1800-2023 §11.6/§11.8 rules
    verbatim: self-determined type bottom-up (`ctype`), the type
    propagated to context-determined operands, operands extended
    (sign-extended only under a signed propagated type), every result
    wrapped to the propagated width (`canonInt`). This is what makes
    `K + 3'd4` with `K = 3'd5` evaluate to `1`, as in every simulator,
    not `9` (verifier finding 2026-10-28). slang's elaborated tree
    carries context propagation as `Resize` nodes (and, in a parametric
    family, resized literals), but their widths are the DEFAULT point's
    (round 3 repair): `ctype` reads a conversion as its operand's own
    type (a 4-state → 2-state `Squash2` too, round 5, and the context
    reaches through one, round 6: `PExpr.ctxPropagates`), `evalAt` converts
    to the context it is given, and the context
    of a root is supplied — the declared width of a typed localparam or
    parameter default at THESE parameters (`evalAssign`), 32 bits for an
    `integer`/`int` one (`evalIntTarget`, round 4), the root's own width
    for a self-determined root (`evalSized`), and, where the tree records
    an outside assignment-like target (a conversion at the root — a genvar
    initializer, an INT-class override into a typed parameter wider than
    32 bits), the own-width value where the target's reading agrees and a loud refusal
    where it differs (`PExpr.pushedTarget`, round 4: the oracles split).
    An untyped parameter default or localparam whose own-type value wraps
    is loud (`evalUntyped`, round 5: Icarus 12.0 evaluates it losslessly),
    and so, since round 6, is every one built with `+ - * **` on its
    context chain, whatever its value (`PExpr.icarusWidens`: Icarus 12.0
    gives it a lossless WIDTH — `N + 1` is 33 bits there, 32 in slang and
    Yosys 0.53 — which shows wherever the width does).
    Division/modulo by zero, x/z operands and out-of-range constant
    selects read x — loud in this tier.
  `parameter int unsigned`, `logic [31:0]` and other typed parameters
  are NOT `int` — the envelope's `signed` field (absent = signed exactly
  when the declared width is 32, a rule only a type of literal bounds may
  rely on, round 5) decides the class (`declConstType`); a
  ranged parameter without a type (`parameter [3:0] V`) is typed.
* **Untyped parameters** take the type of their final value (§6.20.2):
  `instantiate`/`instantiate2` read every argument as an integer OVERRIDE
  (an `int`); `PDesign.atPoint` models a point where some are NOT
  overridden by retyping those to their default's type, and a
  value-position read of one that IS overridden while its default was not
  `int`-typed is loud (`PParam.overrideRetypes`, `IEnv.stale`) — the
  envelope's value tree was typed at the default.
* **32-bit `int` overflow** is not modelled on the fast path;
  `IEnv.int32` evaluates INT parameters width-exactly instead, and
  `Param2.lean`'s `PDesign.int32Agrees` compares the two instantiations
  (the differential runner and `load_design_sv2` refuse a mismatch).
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

/-- Binary operators of the sv-0.2 envelope: the M0 set (`.m0`), integer
and runtime multiplication (`*`), constant-position extras (`/ % ** << >> <<< >>>`), signed order
comparisons (spelled `s<` … by the extractor), and the legacy spellings of
case equality and logical operators. Wildcard comparisons use `.m0`. -/
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
  | .m0 .add => "+" | .m0 .sub => "-" | .m0 .mul => "*"
  | .m0 .div => "u/" | .m0 .sdiv => "s/"
  | .m0 .rem => "u%" | .m0 .srem => "s%"
  | .m0 (.pow signedBase signedExponent) =>
      (if signedBase then "s" else "u") ++ "**" ++ (if signedExponent then "s" else "u")
  | .m0 (.shl signedLeft) => (if signedLeft then "s" else "u") ++ "<<"
  | .m0 (.shr signedLeft) => (if signedLeft then "s" else "u") ++ ">>"
  | .m0 (.ashl signedLeft) => (if signedLeft then "s" else "u") ++ "<<<"
  | .m0 (.ashr signedLeft) => (if signedLeft then "s" else "u") ++ ">>>"
  | .m0 .and => "&" | .m0 .or => "|"
  | .m0 .xor => "^" | .m0 .eq => "==" | .m0 .ne => "!="
  | .m0 .caseEq => "===" | .m0 .caseNe => "!=="
  | .m0 .wildEq => "==?" | .m0 .wildNe => "!=?"
  | .m0 .land => "&&" | .m0 .lor => "||" | .m0 .lt => "<"
  | .m0 .le => "<=" | .m0 .gt => ">" | .m0 .ge => ">="
  | .m0 .slt => "s<" | .m0 .sle => "s<="
  | .m0 .sgt => "s>" | .m0 .sge => "s>="
  | .mul => "*" | .div => "/" | .mod => "%" | .pow => "**"
  | .shl => "<<" | .shr => ">>" | .ashl => "<<<" | .ashr => ">>>"
  | .slt => "s<" | .sle => "s<=" | .sgt => "s>" | .sge => "s>="
  | .ceq => "===" | .cne => "!==" | .land => "&&" | .lor => "||"

/-- Unary operators: the M0 set plus unary `+` and the generate-step
`++`/`--` (which are legal only in `GenerateFor.step` position). -/
inductive SymUnaryOp where
  | m0 (op : UnaryOp)
  | plus  -- unary `+` (arithmetic x/z collapse at runtime)
  | inc   -- `++` (generate step only)
  | dec   -- `--` (generate step only)
deriving Repr, BEq, DecidableEq, Inhabited

/-- The four sv-0.2 system functions (expression position, one argument). -/
inductive SysFn where
  | clog2 | bits | high | size
deriving Repr, BEq, DecidableEq, Inhabited

def SysFn.sym : SysFn → String
  | .clog2 => "$clog2" | .bits => "$bits" | .high => "$high" | .size => "$size"

/-- Trailing part-select form of a packed-array select path
(`PExpr.arrayPart` / `PLhs.arrayPart`): `[a:b]` (`range` — `a`/`b` the msb/
lsb LABELS as written), `[a +: b]` (`up`) and `[a -: b]` (`down` — `a` the
base label, `b` the width), IEEE 1800-2023 §11.5.1. -/
inductive PartMode where
  | range | up | down
deriving Repr, BEq, DecidableEq, Inhabited

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
  | signedResize (width : Nat) (arg : PExpr)
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
  /-- Semantic tier: a packed-array select PATH over the declared signal
  `name` — `name[i₁]…[iₖ]`, element selects outermost first, each index the
  RAW declared label (an elaboration-time constant). Lowered against the
  declaration's packed dimensions (`IEnv.dims`, evaluated in the
  declaration scope) at instantiation:
  per-dimension label→offset normalization (ascending, descending,
  non-zero-based ranges) and range checks, flat `slice` result
  (`Param2.lean`, `arrayElemWindow`/`arrayPartGeom`). The envelope's `ArraySel` node. -/
  | arrayElem (name : String) (indices : List PExpr)
  /-- `arrayElem`'s path followed by a part select on the NEXT dimension:
  `[a:b]`, `[a +: b]`, `[a -: b]` (`PartMode`). -/
  | arrayPart (name : String) (indices : List PExpr) (mode : PartMode) (a b : PExpr)
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
  /-- Signedness of the declared type (envelope `signed`); `none` = the
  envelope default: signed exactly when the declared width is 32 (`int`,
  `integer`), unsigned otherwise (`logic [..]`, `bit`) — the extractor
  emits the field for types that depart from it (`int unsigned`,
  `logic [31:0]`, `byte`, …) and, since round 5, for every type whose
  width depends on a parameter (`declConstType` refuses one without it).
  Meaningless without `type?`. -/
  signed? : Option Bool := none
  /-- An UNTYPED parameter whose type at the DEFAULT point (where slang
  elaborated the envelope: its default's type, §6.20.2) is not the type an
  integer override gives it (`int`). At an overridden point the envelope's
  value-tier tree — operator signedness, conversions — was typed for the
  default's type, so value-position reads of it are loud there (`IEnv.stale`,
  `bindParams`). Set at load by `PDesign.markOverrideRetypes`. -/
  overrideRetypes : Bool := false
deriving Repr, BEq, Inhabited

/-- A `localparam` (evaluated from the bound parameters at
instantiation, in declaration order). `type?`/`signed?` as on `PParam`. -/
structure PLocalParam where
  name : String
  expr : PExpr
  resolved? : Option Int := none
  type? : Option PType := none
  signed? : Option Bool := none
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
  /-- Declared signedness, retained for symbolic scalar/vector declarations. -/
  isSigned : Bool := false
  twoState : Bool := false
  isInput : Bool := false
  isOutput : Bool := false
  isNet : Bool := false
  init : Option PExpr := none
deriving Repr, BEq, Inhabited

/-- Assignment targets of the semantic tier: whole signal, bit/element
select, constant part select, or a concatenation of those direct leaves.
Concatenation targets are used by continuous assignments; their leaves stay
over declared signal names so the comb driver can update each existing
vector window without introducing aggregate storage. -/
inductive PLhs where
  | ident (name : String)
  | bitSel (name : String) (index : PExpr)
  | partSel (name : String) (msb lsb : PExpr)
  | concat (parts : List PLhs)
  /-- A packed-array select path target (`PExpr.arrayElem`'s shape —
  `pp[i][j] = …`): lowered to ONE flat window of the declared vector. -/
  | arrayElem (name : String) (indices : List PExpr)
  /-- … with a trailing part select (`PExpr.arrayPart`'s shape). -/
  | arrayPart (name : String) (indices : List PExpr) (mode : PartMode) (a b : PExpr)
deriving Repr, BEq, Inhabited

/-- The targeted signal's name. -/
def PLhs.name : PLhs → String
  | .ident n | .bitSel n _ | .partSel n _ _ | .arrayElem n _ | .arrayPart n .. => n
  | .concat (part :: _) => part.name
  | .concat [] => ""

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

/-- One segment of a module instance's lexical generate path (F3): the
generate block's name (`genblk<n>` for an unnamed block, IEEE 1800-2023
§27.6) and, for a generate-for block, its genvar — whose value at expansion
time is the block's index (`g_bit[3]`). -/
structure PPathSeg where
  label : String
  genvar : Option String := none
deriving Repr, BEq, Inhabited

/-- One port connection of a module instance, in the CHILD's port order
(the extractor resolves named, ordered, `.name` and `.*` connections).
`input`: the actual is a value expression of the instantiating scope
(`none` = unconnected; `net` = the port is a net, so an unconnected one
reads z — a variable port reads its initial x). `output`: the actual is an
assignment target of the instantiating scope (`none` = unconnected).
`unsupported`: a loud connection (inout, interface port, port default, …). -/
inductive PConn where
  | input (port : String) (actual : Option PExpr) (net : Bool)
  | output (port : String) (actual : Option PLhs)
  | unsupported (port : String) (svKind text : String)
deriving Repr, BEq, Inhabited

/-- The connected port's name (`""` for a loud connection without one). -/
def PConn.port : PConn → String
  | .input p _ _ | .output p _ | .unsupported p _ _ => p

/-- A module instance (F3): instance name, definition name (looked up in
the envelope's module library at instantiation), lexical generate path,
the OVERRIDDEN parameters as `(child parameter, symbolic constant
expression of the instantiating scope)`, and the port connections. The
hierarchical instantiation (`Hier2.lean`, `PDesign.instantiateH`) flattens
it; the flat instantiations (`instantiate`, `instantiate2`) keep it as a
loud unsupported process. -/
structure PInst where
  name : String
  module : String
  path : List PPathSeg := []
  params : List (String × PExpr) := []
  conns : List PConn := []
deriving Repr, BEq, Inhabited

/-- Generate items. `genFor` is ONE structural node — genvar, symbolic
`init`/`bound`/`step`, body **template** (never unrolled in the data);
`genIf` keeps its symbolic condition (`elseB = []` when there is no else
branch; else-if chains are an `elseB` containing one `genIf`).
`resolvedCount?` is defaults-elaborated metadata. `inst` is a module
instance (F3) — at module level or inside a generate body. -/
inductive GenItem where
  | process (p : PProcess)
  | genFor (label : Option String) (genvar : String) (init bound step : PExpr)
      (resolvedCount? : Option Nat) (body : List GenItem)
  | genIf (cond : PExpr) (thenB elseB : List GenItem)
  | unsupported (svKind : String) (text : String)
  | inst (i : PInst)
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
  /-- The packed dimensions of every declaration with an explicit
  dimension list (`PType.packed`), outermost first, as `(msb, lsb)` LABELS
  evaluated ONCE in the declaration's own scope (the module parameters and
  localparams — `Param2.lean`'s `dimTable`, run by `instantiate2` before
  generate expansion): the geometry of packed-array select paths
  (`PExpr.arrayElem`/`arrayPart`, semantic tier). Evaluated rather than
  symbolic so that no genvar bound later by `bindVal` (which may legally
  reuse a parameter's name) can reach a declared range. -/
  dims : List (String × List (Int × Int)) := []
  /-- Parameters/localparams whose type is NOT the INT class (32-bit
  signed): `(name, value, width, signed)`, the value canonical for the
  type (`canonInt`). `vals` is consulted first, so a genvar reusing such a
  name shadows it. Membership in `vals` is what makes a `ParamRef` INT
  (`PExpr.isInt`) — a proof holding `env.vals.lookup n = some v` needs no
  separate typing fact. -/
  nvals : List (String × (Int × Nat × Bool)) := []
  /-- Constants whose type HERE differs from the type the envelope's tree
  was elaborated at (`PParam.overrideRetypes` parameters at an override,
  and untyped localparams defined from them): bound in `nvals` (their
  constant-tier value and type are exact), but a value-position read of one
  is loud (`instExpr2`) — the tree's operator signedness around it is the
  default point's. -/
  stale : List String := []
  /-- **Exact 32-bit `int` mode** (`PDesign.int32Agrees`): INT-class
  parameters and typed-`int` localparams bind in `nvals` at `(32, signed)`
  instead of `vals`, so every constant expression over them is evaluated
  width-exactly (`evalSized`: two's-complement wrap at 32 bits, as in every
  simulator) rather than on the unbounded fast path. Off in `instantiate2`
  (the proof-facing family); the differential runner and the load gate
  compare the two instantiations. -/
  int32 : Bool := false
  /-- The packed range of every TYPED parameter/localparam whose declared
  bounds are not all literals (`localparam logic [N-1:0] P`), evaluated at
  THIS point (`bindParams`/`bindLocal`, round 3 folds). The extractor keeps
  a select of such a parameter's value (`P[1]`, `P[0 +: 2]`) in the legacy
  encoding — its labels read as offsets from bit 0 — only where the range is
  canonical `[m:0]` at the default point (`_sym_param_root_select`); the
  constant tier (`evalAt`, `paramSelectOk`) refuses the select at a point
  where the range is anything else (`[-1:0]` at `N = 0`). Parameters with
  literal bounds (offsets folded by the extractor, exact everywhere) and
  INT-class ones (`[31:0]`) are absent. -/
  pdims : List (String × List (Int × Int)) := []
deriving Repr, Inhabited

/-- Bind a constant (prepend — shadows outer bindings of the name). -/
def IEnv.bindVal (env : IEnv) (n : String) (v : Int) : IEnv :=
  { env with vals := (n, v) :: env.vals }

/-- Bind a non-INT typed constant (`IEnv.nvals`). -/
def IEnv.bindNVal (env : IEnv) (n : String) (v : Int) (w : Nat) (s : Bool) : IEnv :=
  { env with nvals := (n, (v, w, s)) :: env.nvals }

/-! ## Constant tier: `evalInt` -/

private def b2i (b : Bool) : Int := if b then 1 else 0

/-- `v` at the constant type `(w, s)`: two's complement modulo `2^w`, read
signed when `s` (IEEE 1800-2023 §11.8.2: every operation is carried out at
the propagated width; `canonInt w s` is the value that width holds). -/
def canonInt (w : Nat) (s : Bool) (v : Int) : Int :=
  let m := v.emod ((2 : Int) ^ w)
  if s && decide (0 < w) && decide ((2 : Int) ^ (w - 1) ≤ m) then m - (2 : Int) ^ w else m

/-- A value of type `(lw, ls)` at the propagated type `(w, s)` (§11.8.2:
the operand's bits extended — sign-extended ONLY when the propagated type
is signed — or truncated, then read at the new type). -/
def convertConst (lw : Nat) (w : Nat) (s : Bool) (v : Int) : Int :=
  let bits := v.emod ((2 : Int) ^ lw)
  canonInt w s (if s then canonInt lw true bits else bits)

/-- How a binary operator treats its operands in a constant expression
(IEEE 1800-2023 §11.6.1 Table 11-21). -/
inductive ConstOpClass where
  /-- `+ - * / % & | ^`: context-determined operands (the max width, signed
  iff both are). -/
  | arith
  /-- `<< >> <<< >>> **`: the left operand context-determined, the right
  self-determined. -/
  | shift
  /-- Equality/relational: operands sized to each other, 1-bit unsigned
  result. -/
  | compare
  /-- `&& ||`: self-determined operands, 1-bit unsigned result. -/
  | logical
  /-- The run-time vector spellings (`u/`, `s%`, `u**s`, `s>>` …): loud in a
  constant context. -/
  | vector
deriving Repr, BEq, DecidableEq, Inhabited

/-- `ConstOpClass` of an envelope operator. -/
def SymBinOp.constClass : SymBinOp → ConstOpClass
  | .m0 .add | .m0 .sub | .m0 .mul | .m0 .and | .m0 .or | .m0 .xor
  | .mul | .div | .mod => .arith
  | .pow | .shl | .shr | .ashl | .ashr => .shift
  | .m0 .eq | .m0 .ne | .m0 .caseEq | .m0 .caseNe | .m0 .wildEq | .m0 .wildNe
  | .m0 .lt | .m0 .le | .m0 .gt | .m0 .ge
  | .m0 .slt | .m0 .sle | .m0 .sgt | .m0 .sge
  | .slt | .sle | .sgt | .sge | .ceq | .cne => .compare
  | .m0 .land | .m0 .lor | .land | .lor => .logical
  | _ => .vector

/-- The operators that keep the INT class (32-bit signed operands in,
32-bit signed result out). -/
def SymBinOp.intArith : SymBinOp → Bool
  | .m0 .add | .m0 .sub | .m0 .mul | .m0 .and | .m0 .or | .m0 .xor
  | .mul | .div | .mod | .pow | .shl | .shr | .ashl | .ashr => true
  | _ => false

/-- **The INT class** of a constant expression: built from unsized integers,
genvars, system-call results and `vals`-bound (32-bit signed) parameters by
the `intArith` operators, unary `-`/`+`, and `?:` (whose condition is
self-determined and may be anything). Its value is the mathematical one
(`evalInt`'s fast path, the ledger's unbounded-`Int` regime); every other
expression is evaluated width-exactly by `evalSized`. A `ParamRef` is INT
exactly when the name is bound in `IEnv.vals` (non-INT typed parameters
live in `IEnv.nvals`). -/
def PExpr.isInt (env : IEnv) : PExpr → Bool
  | .int _ | .genvarRef _ | .sysCall .. => true
  | .paramRef n none => (env.vals.lookup n).isSome
  | .unary (.m0 .neg) a | .unary (.m0 .pos) a | .unary .plus a => a.isInt env
  | .binary op l r => op.intArith && l.isInt env && r.isInt env
  | .ternary _ t e => t.isInt env && e.isInt env
  | _ => false

-- The INT-class test computes on syntax (and `vals` lookups): a `simp` that
-- unfolds `evalInt` decides it by itself.
attribute [simp] PExpr.isInt SymBinOp.intArith

mutual
/-- Whether a `ParamRef` to one of `names` occurs anywhere in the
expression (`IEnv.stale` propagation and value-tier checks). -/
def PExpr.mentionsAny (names : List String) : PExpr → Bool
  | .paramRef n _ => names.contains n
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a | .sysCall _ a
  | .reduce _ a | .cast _ a => a.mentionsAny names
  | .binary _ l r | .bitSel l r | .repl l r => l.mentionsAny names || r.mentionsAny names
  | .partSel b m l | .ternary b m l =>
      b.mentionsAny names || m.mentionsAny names || l.mentionsAny names
  | .concat ps | .arrayElem _ ps => PExpr.mentionsAnyList names ps
  | .arrayPart _ ps _ a b =>
      PExpr.mentionsAnyList names ps || a.mentionsAny names || b.mentionsAny names
  | .lit _ | .ident _ | .genvarRef _ | .enumRef .. | .int _ | .fill _
  | .unsupported .. => false

/-- `PExpr.mentionsAny` over a list. -/
def PExpr.mentionsAnyList (names : List String) : List PExpr → Bool
  | [] => false
  | p :: ps => p.mentionsAny names || PExpr.mentionsAnyList names ps
end

/-- An order comparison spelled signed by the frontend (`s<` …). -/
private def SymBinOp.signedOrder : SymBinOp → Bool
  | .m0 .slt | .m0 .sle | .m0 .sgt | .m0 .sge | .slt | .sle | .sgt | .sge => true
  | _ => false

/-- An order comparison spelled UNSIGNED by the frontend (plain `<` …:
slang spells every signed comparison `s<`). -/
private def SymBinOp.unsignedOrder : SymBinOp → Bool
  | .m0 .lt | .m0 .le | .m0 .gt | .m0 .ge => true
  | _ => false

/-- `+ - * / % & | ^` at `(w, s)` on operands already at that type. -/
private def constArith (op : SymBinOp) (w : Nat) (s : Bool) (a b : Int) : Except String Int :=
  match op with
  | .m0 .add => .ok (canonInt w s (a + b))
  | .m0 .sub => .ok (canonInt w s (a - b))
  | .m0 .mul | .mul => .ok (canonInt w s (a * b))
  | .div => if b == 0 then .error "division by zero in a constant context (reads x)"
            else .ok (canonInt w s (a.tdiv b))
  | .mod => if b == 0 then .error "modulo by zero in a constant context (reads x)"
            else .ok (canonInt w s (a.tmod b))
  | .m0 .and | .m0 .or | .m0 .xor =>
      let x := (a.emod ((2 : Int) ^ w)).toNat
      let y := (b.emod ((2 : Int) ^ w)).toNat
      .ok (canonInt w s (Int.ofNat (match op with
        | .m0 .and => x &&& y
        | .m0 .or => x ||| y
        | _ => x ^^^ y)))
  | _ => .error s!"operator '{op.sym}' outside the constant tier"

/-- `<< <<< >> >>> **` at `(w, s)`: `a` at that type, `b` the
self-determined right operand (a shift amount is unsigned in SV; a
negative constant one is loud here, as is a negative exponent). -/
private def constShift (op : SymBinOp) (w : Nat) (s : Bool) (a b : Int) : Except String Int :=
  if b < 0 then .error s!"negative right operand of '{op.sym}' in a constant context"
  else
    match op with
    | .shl | .ashl =>
        if (w : Int) ≤ b then .ok 0 else .ok (canonInt w s (a * (2 : Int) ^ b.toNat))
    | .shr =>
        if (w : Int) ≤ b then .ok 0
        else .ok (canonInt w s (a.emod ((2 : Int) ^ w) / (2 : Int) ^ b.toNat))
    | .ashr =>
        if s then
          if (w : Int) ≤ b then .ok (if a < 0 then -1 else 0)
          else .ok (a.fdiv ((2 : Int) ^ b.toNat))
        else if (w : Int) ≤ b then .ok 0
        else .ok (canonInt w s (a.emod ((2 : Int) ^ w) / (2 : Int) ^ b.toNat))
    | .pow =>
        if 4096 < b then .error "'**' exponent above 4096 in a constant context"
        else .ok (canonInt w s (a ^ b.toNat))
    | _ => .error s!"operator '{op.sym}' outside the constant tier"

/-- Equality/relational result on operands at their common type. -/
private def constCompare (op : SymBinOp) (a b : Int) : Int :=
  match op with
  | .m0 .ne | .m0 .caseNe | .m0 .wildNe | .cne => b2i (a != b)
  | .m0 .lt | .m0 .slt | .slt => b2i (decide (a < b))
  | .m0 .le | .m0 .sle | .sle => b2i (decide (a ≤ b))
  | .m0 .gt | .m0 .sgt | .sgt => b2i (decide (a > b))
  | .m0 .ge | .m0 .sge | .sge => b2i (decide (a ≥ b))
  | _ => b2i (a == b)

/-- **A constant select of a parameter's value reads labels as offsets
exactly** (round 3 folds, `IEnv.pdims`): a parameter whose declared range
is parameter-dependent must be ONE dimension `[m:0]` with `m ≥ 0` at this
point. The extractor emits such a select only where the range is canonical
at the default point (`_sym_param_root_select`), with its labels raw; at a
point where the range is `[-1:0]` (`[N-1:0]` at `N = 0`), label 1 is out of
range — Icarus 12.0 and Yosys 0.53 read x, the offset reading a bit of the
value — so the select is refused here, loudly. Every other base passes. -/
def paramSelectOk (env : IEnv) : PExpr → Except String Unit
  | .paramRef n none =>
      match env.pdims.lookup n with
      | none => .ok ()
      | some [(l, r)] =>
          if r == 0 && decide (0 ≤ l) then .ok ()
          else .error s!"select of parameter '{n}', whose packed range is [{l}:{r}] at these parameters: the envelope reads its labels as offsets from bit 0, exact only on a range [m:0] with m ≥ 0"
      | some ds =>
          .error s!"select of parameter '{n}', which has {ds.length} packed dimensions at these parameters (the constant tier selects bits of one dimension)"
  | _ => .ok ()

/-- **`$size`/`$high` of a declared signal at this point** (round 3 folds,
IEEE 1800-2023 §20.7): its FIRST (outermost) packed dimension as evaluated
in `IEnv.dims` — `$high` the larger label, `$size` the element count
`|msb - lsb| + 1`. They used to be read as `width - 1` and `width`, i.e.
for a 1-D `[W-1:0]` range: `$high` of `logic [7:4] u` is 7, not 3; of
`logic [N-1:0] v` at `N = 0` (the ascending `[-1:0]`) 0, not 1; `$size` of
`logic [3:0][7:0] m` is 4, not 32. A signal without a dimension entry here
(an enum- or struct-typed declaration, a scalar, a range that does not
evaluate, or a dimension bound read before the table exists) is loud. -/
def dimQuery (env : IEnv) (fn : String) (n : String) (high : Bool) : Except String Int :=
  match env.dims.lookup n with
  | some ((l, r) :: _) => .ok (if high then max l r else ((l - r).natAbs + 1 : Nat))
  | _ => .error s!"{fn} of '{n}': its packed range is not known here (only a declared signal with an explicit packed dimension list, after the declaration scope is built)"

/-- **Context-propagating operators** (IEEE 1800-2023 §11.6.1, §11.8.2):
the nodes whose operands take the width of the expression's context —
unary `- ~ +`, binary `+ - * / % & | ^`, the left operand of a shift or
power, and the arms of `?:`. A `Resize` the envelope wraps around one of
them (an assignment-like truncation at the DEFAULT point: `c = a + b` with
a 2-bit `c` and 4-bit operands) is no truncation at a point where the
context is wider: there the operands are extended BEFORE the operation and
its carry survives (`instExpr2`'s `resize` arm and `evalAt`'s, round 3
folds, repros `sx` and `vp_lp2`). Every other node — a leaf, a select, a
comparison, a reduction, a concatenation, a cast — is self-determined
under the conversion.

Round 6 folds (round 5 FOLDS verifier blocker 1, repro `vs_sqn`): a
`Squash2` is transparent here exactly as it is to `ctype` (round 5). A
2-state target NARROWER than its initializer at the default point is
`Resize(target, Squash2(default width, op))` in slang's tree; with the
`Squash2` opaque, the `resize` arm evaluated `op` at its OWN width at a
point where the target is the wider context: `localparam shortint H1 =
(U + 1'b1) >> 1` with a 4-bit `U = 15` was 0 where Icarus 12.0, the
Yosys 0.53 netlist and slang's elaboration give 8 (also `byte`, `bit
[7:0]`, `bit signed [7:0]`, a `byte` parameter default, and an `int` over
an operand wider than 32 bits at the default point). The value tier
refuses every `Squash2` (`instExpr2`), so only the constant tier reads
this. -/
def PExpr.ctxPropagates : PExpr → Bool
  | .unary (.m0 .lnot) _ => false
  | .unary (.m0 _) _ | .unary .plus _ => true
  | .binary op _ _ =>
      match op with
      | .m0 .add | .m0 .sub | .m0 .mul | .m0 .and | .m0 .or | .m0 .xor
      | .m0 .div | .m0 .sdiv | .m0 .rem | .m0 .srem | .m0 (.pow ..)
      | .m0 (.shl _) | .m0 (.shr _) | .m0 (.ashl _) | .m0 (.ashr _)
      | .mul | .div | .mod | .pow | .shl | .shr | .ashl | .ashr => true
      | _ => false
  | .ternary .. => true
  | .squash2 _ a => a.ctxPropagates
  | _ => false

/-- Whether an operand is a `Squash2` node (round 7 folds): the operand whose
context reading round 6 introduced (`PExpr.ctxPropagates`), and whose
own-width reading `evalAt`'s `resize`, `signedResize` and `squash2` arms
still require to be DEFINED (the round 7 gate there). -/
def PExpr.isSquash2 : PExpr → Bool
  | .squash2 .. => true
  | _ => false

/-- The refusal of a NEGATIVE genvar zero-extended past its 32 bits
(`PExpr.negGenvarAt`, and `PExpr.negGenvarWidened` in the value tier). -/
def negGenvarMsg (g : String) (w : Nat) : String :=
  s!"genvar '{g}' is negative here and is extended into an unsigned {w}-bit context: Icarus 12.0 sign-extends it, Yosys 0.53, Verilator 5.042 and the LRM (§27.4, §11.8.2) zero-extend it"

/-- **Where the oracles split**, constant tier (round 3 folds): the
operand of an unsigned conversion that is a NEGATIVE genvar, at a context
wider than its 32 bits — Icarus 12.0 sign-extends it, Yosys 0.53,
Verilator 5.042 and the LRM zero-extend it (`negGenvarMsg`). -/
def PExpr.negGenvarAt (env : IEnv) (w : Nat) : PExpr → Option String
  | .genvarRef g =>
      match env.vals.lookup g with
      | some v => if v < 0 && 32 < w then some g else none
      | none => none
  | _ => none

mutual
/-- **Self-determined type** `(width, signed)` of a constant expression
(IEEE 1800-2023 §11.6.1 Table 11-21, §11.8.1): unsized integers, genvars,
system calls and INT parameters are `(32, signed)`; a sized literal its own
width, unsigned (a signed literal arrives as `cast true` — `Ingest2`); a
typed parameter its declared type; context-determined operators the max of
their operands, signed iff both are; comparisons/logical/`!`/selects
unsigned; shifts and `**` the left operand's type. -/
def ctype (env : IEnv) : PExpr → Except String (Nat × Bool)
  | .int _ | .genvarRef _ | .sysCall .. => .ok (32, true)
  | .lit v => .ok (v.width, false)
  | .paramRef n none =>
      match env.vals.lookup n with
      | some _ => .ok (32, true)
      | none =>
          match env.nvals.lookup n with
          | some (_, w, s) => .ok (w, s)
          | none => .error s!"unbound parameter '{n}'"
  | .paramRef n (some p) => .error s!"package-scoped parameter '{p}::{n}'"
  | .enumRef ty _ _ =>
      match env.enums.lookup ty with
      | some w => .ok (w, false)
      | none => .error s!"unknown enum type '{ty}'"
  | .unary op a =>
      match op with
      | .m0 .lnot => .ok (1, false)
      | .m0 .neg | .m0 .pos | .m0 .bnot | .plus => ctype env a
      | .inc | .dec => .error "'++'/'--' outside a generate step"
  | .binary op l r =>
      match op.constClass with
      | .arith => do
          let (wl, sl) ← ctype env l
          let (wr, sr) ← ctype env r
          .ok (max wl wr, sl && sr)
      | .shift => ctype env l
      | .compare | .logical => .ok (1, false)
      | .vector => .error s!"vector operator '{op.sym}' in a constant context"
  | .ternary _ t e => do
      let (wt, st) ← ctype env t
      let (we, se) ← ctype env e
      .ok (max wt we, st && se)
  -- Round 3 folds (verifier finding, `vp_lp2`/`c_intlp`): an implicit
  -- conversion's envelope width is the DEFAULT point's context, so it is
  -- transparent here — what a conversion contributes to the max-of-operands
  -- width at THESE parameters is its operand's own width (`selfWidth2`'s
  -- reading in the value tier); the context it converts to is supplied
  -- from above (`evalAt`'s `ty`, an assignment target through
  -- `evalAssign`/`evalIntTarget`; round 4: never a width read off a
  -- conversion, which `evalSized` uses only to REFUSE a root whose outside
  -- target's reading differs, `PExpr.pushedTarget`). A `Squash2` is
  -- transparent too (round 5 folds, verifier repro `vq_sq2`): its width is
  -- the 2-state TARGET's at the default point (`bit [N-1:0] B = …` at
  -- `N = 32`) or its operand's there, and keeping it as a floor evaluated
  -- `(U + 1'b1) >> 1` at 32 bits at `N = 4` (8 where every tool gives 0);
  -- the target is supplied from above (`evalAssign` at the declared width,
  -- `evalIntTarget` for an `int`).
  | .resize _ a => do
      let (wa, _) ← ctype env a
      .ok (wa, false)
  | .signedResize _ a => do
      let (wa, _) ← ctype env a
      .ok (wa, true)
  | .squash2 _ a => ctype env a
  | .cast s a => do
      let (w, _) ← ctype env a
      .ok (w, s)
  | .bitSel .. => .ok (1, false)
  | .partSel b m l => do
      let _ ← ctype env b  -- a signal base is loud before its bounds are read
      let mv ← evalAt env (← ctype env m) m
      let lv ← evalAt env (← ctype env l) l
      if lv ≤ mv then .ok ((mv - lv).toNat + 1, false) else .error "bad part-select bounds"
  | .ident n => .error s!"signal '{n}' in a constant context"
  | .arrayElem n _ | .arrayPart n .. => .error s!"signal '{n}' in a constant context"
  | .fill _ => .error "unbased-unsized literal in a constant context (no context width)"
  | .concat _ => .error "concatenation in a constant context"
  | .repl _ _ => .error "replication in a constant context"
  | .reduce _ _ => .error "reduction in a constant context (width-dependent)"
  | .unsupported k _ => .error s!"unsupported node '{k}' in a constant context"

/-- **Value at a propagated type** `ty = (w, s)` (IEEE 1800-2023 §11.8.2):
context-determined operands are evaluated at `ty` itself, self-determined
ones (shift amounts, exponents, conditions, select labels, comparison and
logical operands, cast/resize operands) at their own `ctype`; leaves are
converted with `convertConst`; every result is `canonInt w s`. Loud on x/z,
division by zero, out-of-range constant selects, and a frontend
signed/unsigned comparison spelling the operand types contradict (the
envelope's typing and ours must agree — a missing `signed` field shows up
here, never as a silently different answer). -/
def evalAt (env : IEnv) (ty : Nat × Bool) : PExpr → Except String Int
  | .int v => .ok (convertConst 32 ty.1 ty.2 v)
  | .lit v =>
      match v.toNat? with
      | some n => .ok (convertConst v.width ty.1 ty.2 n)
      | none => .error "x/z literal in a constant context"
  | .paramRef n none =>
      match env.vals.lookup n with
      | some v => .ok (convertConst 32 ty.1 ty.2 v)
      | none =>
          match env.nvals.lookup n with
          | some (v, w, _) => .ok (convertConst w ty.1 ty.2 v)
          | none => .error s!"unbound parameter '{n}'"
  | .paramRef n (some p) => .error s!"package-scoped parameter '{p}::{n}'"
  | .genvarRef n =>
      match env.vals.lookup n with
      | some v => .ok (convertConst 32 ty.1 ty.2 v)
      | none => .error s!"genvar '{n}' outside its loop"
  | .enumRef tn mem _ =>
      match env.members.lookup (tn, mem) with
      | some v =>
          match v.toNat? with
          | some k => .ok (convertConst v.width ty.1 ty.2 k)
          | none => .error s!"enum member {tn}::{mem} has x/z bits"
      | none => .error s!"unknown enum member {tn}::{mem}"
  | .sysCall fn a =>
      match fn, a with
      | .clog2, e => do
          let v ← evalAt env (← ctype env e) e
          if v < 0 then .error "$clog2 of a negative value"
          else .ok (convertConst 32 ty.1 ty.2 (clog2 v.toNat : Int))
      | .bits, .ident n =>
          match env.widths.lookup n with
          | some w => .ok (convertConst 32 ty.1 ty.2 (w : Int))
          | none => .error s!"$bits/$size of undeclared signal '{n}'"
      | .size, .ident n => do
          let v ← dimQuery env "$size" n false
          .ok (convertConst 32 ty.1 ty.2 v)
      | .high, .ident n => do
          let v ← dimQuery env "$high" n true
          .ok (convertConst 32 ty.1 ty.2 v)
      | f, _ => .error s!"{f.sym} argument outside the declared-signal tier"
  | .unary op a =>
      match op with
      | .m0 .lnot => do
          let x ← evalAt env (← ctype env a) a
          .ok (convertConst 1 ty.1 ty.2 (b2i (x == 0)))
      | .m0 .neg => do
          let x ← evalAt env ty a
          .ok (canonInt ty.1 ty.2 (-x))
      | .m0 .bnot => do
          let x ← evalAt env ty a
          .ok (canonInt ty.1 ty.2 (-x - 1))
      | .m0 .pos | .plus => evalAt env ty a
      | .inc | .dec => .error "'++'/'--' outside a generate step"
  | .binary op l r =>
      match op.constClass with
      | .arith => do
          let a ← evalAt env ty l
          let b ← evalAt env ty r
          constArith op ty.1 ty.2 a b
      | .shift => do
          let a ← evalAt env ty l
          let b ← evalAt env (← ctype env r) r
          constShift op ty.1 ty.2 a b
      | .compare => do
          let (wl, sl) ← ctype env l
          let (wr, sr) ← ctype env r
          let ct := (max wl wr, sl && sr)
          if (op.signedOrder && !ct.2) || (op.unsignedOrder && ct.2) then
            .error s!"'{op.sym}' contradicts the operand signedness (constant tier)"
          else do
            let a ← evalAt env ct l
            let b ← evalAt env ct r
            .ok (convertConst 1 ty.1 ty.2 (constCompare op a b))
      | .logical => do
          let a ← evalAt env (← ctype env l) l
          let b ← evalAt env (← ctype env r) r
          let v := match op with
            | .m0 .land | .land => a != 0 && b != 0
            | _ => a != 0 || b != 0
          .ok (convertConst 1 ty.1 ty.2 (b2i v))
      | .vector => .error s!"vector operator '{op.sym}' in a constant context"
  | .ternary c t e => do
      let cv ← evalAt env (← ctype env c) c
      if cv != 0 then evalAt env ty t else evalAt env ty e
  | .resize _ a => do
      -- An UNSIGNED conversion to the CONTEXT `ty` (the envelope's width
      -- is the default point's — round 3 folds, `vp_lp2`): a
      -- context-propagating operand (`PExpr.ctxPropagates` — at a root,
      -- the default point's assignment truncation) is evaluated AT the
      -- context, so its carry survives where the context is wider; any
      -- other operand is its own bits (a signed one — the extractor's
      -- `_sym_unsigned_simple_operand` marker — taken modulo its own
      -- width) zero-extended. A NEGATIVE genvar extended past 32 bits is
      -- where the oracles split (`negGenvarMsg`): loud.
      let (wa, sa) ← ctype env a
      if a.ctxPropagates && decide (wa < ty.1) then do
        -- Round 7 folds (round 6 FOLDS verifier major 4): through a
        -- `Squash2` the context reading is round 6's; the own-width reading
        -- (the round 5 one) must still be defined, so a shape round 5
        -- refused (`4'd8 / (U + 1'b1)` divides by zero at U's 4 bits) stays
        -- loud. The squash2-free twin never had this gate.
        if a.isSquash2 then discard (evalAt env (wa, sa) a)
        let x ← evalAt env (ty.1, sa) a
        .ok (canonInt ty.1 ty.2 x)
      else
        match a.negGenvarAt env ty.1 with
        | some g => .error (negGenvarMsg g ty.1)
        | none => do
            let x ← evalAt env (wa, sa) a
            .ok (canonInt ty.1 ty.2 (x.emod ((2 : Int) ^ wa)))
  | .signedResize _ a => do
      -- A SIGNED conversion to the context: sign extension of the operand's
      -- own value (a context-propagating operand evaluated at the context).
      let (wa, sa) ← ctype env a
      if a.ctxPropagates && decide (wa < ty.1) then do
        -- Round 7 folds: the `Squash2` own-width gate (the `resize` arm).
        if a.isSquash2 then discard (evalAt env (wa, sa) a)
        let x ← evalAt env (ty.1, sa) a
        .ok (canonInt ty.1 ty.2 x)
      else do
        let x ← evalAt env (wa, sa) a
        .ok (convertConst wa ty.1 ty.2 (canonInt wa true x))
  | .squash2 _ a => do
      -- 4-state → 2-state: no width of its own (x/z are loud in this tier).
      let (wa, sa) ← ctype env a
      if a.ctxPropagates && decide (wa < ty.1) then do
        -- Round 7 folds: the `Squash2` own-width gate (the `resize` arm).
        if a.isSquash2 then discard (evalAt env (wa, sa) a)
        let x ← evalAt env (ty.1, sa) a
        .ok (canonInt ty.1 ty.2 x)
      else do
        let x ← evalAt env (wa, sa) a
        .ok (convertConst wa ty.1 ty.2 x)
  | .cast s a => do
      let (wa, sa) ← ctype env a
      let x ← evalAt env (wa, sa) a
      .ok (convertConst wa ty.1 ty.2 (canonInt wa s x))
  | .bitSel base idx => do
      let (wb, sb) ← ctype env base
      paramSelectOk env base
      let bv ← evalAt env (wb, sb) base
      let i ← evalAt env (← ctype env idx) idx
      if i < 0 || (wb : Int) ≤ i then
        .error "constant bit select out of range (reads x)"
      else
        .ok (convertConst 1 ty.1 ty.2
          (Int.ofNat (((bv.emod ((2 : Int) ^ wb)).toNat >>> i.toNat) % 2)))
  | .partSel base m l => do
      let (wb, sb) ← ctype env base
      paramSelectOk env base
      let bv ← evalAt env (wb, sb) base
      let mv ← evalAt env (← ctype env m) m
      let lv ← evalAt env (← ctype env l) l
      if lv < 0 || mv < lv || (wb : Int) ≤ mv then
        .error "constant part select out of range (reads x)"
      else
        let fw := (mv - lv).toNat + 1
        .ok (convertConst fw ty.1 ty.2
          (Int.ofNat (((bv.emod ((2 : Int) ^ wb)).toNat >>> lv.toNat) % 2 ^ fw)))
  | .ident n => .error s!"signal '{n}' in a constant context"
  | .arrayElem n _ | .arrayPart n .. => .error s!"signal '{n}' in a constant context"
  | .fill _ => .error "unbased-unsized literal in a constant context (no context width)"
  | .concat _ => .error "concatenation in a constant context"
  | .repl _ _ => .error "replication in a constant context"
  | .reduce _ _ => .error "reduction in a constant context (width-dependent)"
  | .unsupported k _ => .error s!"unsupported node '{k}' in a constant context"
end

/-- **The outside target of a constant root, where its tree records one**
(round 4 folds): `some w` for a conversion AT THE ROOT (`evalSized`
receives it from `evalInt`'s `resize`/`signedResize` arms). slang writes a
conversion around a whole constant only at the root of an assignment-like
context, and the extractor keeps one where slang made it same-width: a
genvar initializer, wrapped in `Resize(32, …)`/`SignedResize(32, …)`
(`_sym_genvar_init`; its target, a 32-bit `integer`, is the same at every
point), and an INT-class instance override into a typed parameter wider than
32 bits, wrapped at that width (`_sym_override_root`). `none` for every
other root: a select label, a generate condition or bound, a dimension
bound, an untyped localparam or parameter default — SELF-DETERMINED roots,
whose type is their own at THESE parameters (`ctype`). No conversion INSIDE
a root is read as a target: a signed-operand marker, a widened literal or a
widened parameter carries the width of the DEFAULT point's widest operand
(`SB + 1'b1` with `logic signed [N-1:0] SB` is `Resize(8, SB) + Resize(8,
1'b1)` at `N = 8`) — or, in a VALUE position, of a sibling signal (`a + P *
2` with a 33-bit `a` is `a + Resize(33, P) * 2`, `constAtCtx2`) — and
reading it as a target gave a self-determined root the default point's
width (round 3 FOLDS verifier, repros `rf_lbl`, `rf_gen`, `rf_lp`,
`rf_par`). -/
def PExpr.pushedTarget : PExpr → Option Nat
  | .resize w _ | .signedResize w _ => some w
  | _ => none

/-- The refusal of a constant root whose two readings differ
(`evalSized`). -/
def assignCtxMsg (w f : Nat) (v v' : Int) : String :=
  s!"Constant:assignment-context — a constant assigned to a {f}-bit target (a genvar initializer, or an INT-class instance override into a wider typed parameter) is {w} bits wide at these parameters, and its value at its own width ({v}) differs from its value at the target's ({v'}): IEEE 1800-2023 §10.8/§11.8.1, slang and Yosys 0.53 evaluate it at the target's width, Icarus 12.0 at its own (measured on genvar initializers) — refused where the readings differ"

/-- The refusal of a constant root assigned to a 32-bit target whose value
that target's signed `integer` would change (`evalSized`). -/
def assignFitMsg (w f : Nat) (v : Int) : String :=
  s!"Constant:assignment-context — a constant assigned to a {f}-bit target (a genvar initializer) is {w} bits wide at these parameters and its value {v} is not a 32-bit signed integer: IEEE 1800-2023 §27.4 and slang convert a genvar initializer to its `integer` (truncated and read signed), Icarus 12.0 and Yosys 0.53 keep the value whole (measured) — refused"

/-- **Width-exact constant evaluation** (round 4 folds): the value of `e`
at its OWN type at THESE parameters (`ctype` then `evalAt`) — `evalInt`'s
regime for every expression outside the INT class, the reading of every
self-determined root. Where the tree records an outside assignment-like
target (`PExpr.pushedTarget`: a genvar initializer, an INT-class override
into a typed parameter wider than 32 bits), the target's reading is `max(target, own width)`
(§10.8, §11.8.1) while Icarus 12.0 evaluates a genvar initializer at its own
width (repro `rf_gv`: `genvar g = U + 1'b1` with `logic [N-1:0] U = -1`
starts at 0 in Icarus and at 16 in slang's elaboration and the Yosys 0.53
netlist at `N = 4`): the own-width value is returned where the two
readings agree, and the root is REFUSED where they differ
(`Constant:assignment-context`), or where a root assigned to a 32-bit target
has a value that is no 32-bit signed integer (a genvar initializer of
2^32 + 1 is 1 in slang and §27.4, and one of `32'hFFFF_FFFF` is -1, while
Icarus and Yosys keep both whole; the check is keyed on the genvar's 32
bits, so an instance override of such a value into a 32-bit typed
parameter is refused the same way, a recorded over-refusal). The
target width is the default point's metadata, exact for a genvar's 32-bit
`integer` and for an override into a parameter of a fixed type; for one
whose own type is parameter-dependent it is the default point's, and only
the refusal side uses it. Typed localparams and typed parameter defaults, whose target is
known at every point, go through `evalAssign`/`evalIntTarget` instead. -/
def evalSized (env : IEnv) (e : PExpr) : Except String Int := do
  let (w, s) ← ctype env e
  let v ← evalAt env (w, s) e
  match e.pushedTarget with
  | none => .ok v
  | some f =>
      if w < f then do
        let v' ← evalAt env (f, s) e
        if convertConst w f s v == v' then .ok v else .error (assignCtxMsg w f v v')
      else if f == 32 && canonInt 32 true v != v then .error (assignFitMsg w f v)
      else .ok v

/-- **An assignment-like constant context** (§10.8, §11.8.1): `e`'s value
when assigned to a `w`-bit target — evaluated at the context `max w (its
own width at THESE parameters)` with its own signedness (the target's
signedness does not propagate into a right-hand side), before the caller
converts it to the target type (`canonInt`). The typed-localparam and
typed-parameter-default twin of the value tier's `fitExpr2` (round 3
folds, verifier finding `vp_lp2`: `localparam logic [N-1:0] L1 = 8'd200 +
8'd100` is `44` at `N = 8` and `300` at `N = 16`; the envelope's
default-point `Resize(4, …)` used to make it `12` at every point). -/
def evalAssign (env : IEnv) (w : Nat) (e : PExpr) : Except String Int := do
  let (we, se) ← ctype env e
  evalAt env (max w we, se) e

/-- Evaluate a symbolic expression as an integer constant (parameter
defaults, localparams, generate headers/conditions, dimension bounds,
system calls, select labels) at its SELF-DETERMINED type. Loud `.error` on
anything value-tier or unbound. INT-class operands take the mathematical
fast path below (the ledger's unbounded-`Int` regime, unchanged equations
for every proof over genvar/parameter arithmetic); any other operand sends
the node to `evalSized`, the width-exact §11.6/§11.8 evaluation — see the
module docstring. -/
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
      | none =>
          match env.nvals.lookup n with
          | some (v, _, _) => .ok v
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
  | .unary op a =>
      if a.isInt env then do
        let v ← evalInt env a
        match op with
        | .m0 .neg => .ok (-v)
        | .m0 .lnot => .ok (b2i (v == 0))
        | .m0 .bnot => .error "'~' in a constant context (width-dependent)"
        | .m0 .pos | .plus => .ok v
        | .inc | .dec => .error "'++'/'--' outside a generate step"
      else evalSized env (.unary op a)
  | .binary op l r =>
      if l.isInt env && r.isInt env then do
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
        | .m0 .caseEq => .ok (b2i (a == b))
        | .m0 .caseNe => .ok (b2i (a != b))
        | .m0 .wildEq => .ok (b2i (a == b))
        | .m0 .wildNe => .ok (b2i (a != b))
        | .m0 .land => .ok (b2i (a != 0 && b != 0))
        | .m0 .lor => .ok (b2i (a != 0 || b != 0))
        | .m0 .lt | .m0 .slt | .slt => .ok (b2i (decide (a < b)))
        | .m0 .le | .m0 .sle | .sle => .ok (b2i (decide (a ≤ b)))
        | .m0 .gt | .m0 .sgt | .sgt => .ok (b2i (decide (a > b)))
        | .m0 .ge | .m0 .sge | .sge => .ok (b2i (decide (a ≥ b)))
        | .ceq => .ok (b2i (a == b))
        | .cne => .ok (b2i (a != b))
        | .land => .ok (b2i (a != 0 && b != 0))
        | .lor => .ok (b2i (a != 0 || b != 0))
        | .m0 .mul | .mul => .ok (a * b)
        | .m0 .div | .m0 .sdiv | .m0 .rem | .m0 .srem =>
            .error "vector quotient/remainder requires operand widths"
        | .m0 (.pow ..) => .error "vector power requires operand widths"
        | .m0 (.shl ..) | .m0 (.shr ..) | .m0 (.ashl ..) | .m0 (.ashr ..) =>
            .error "vector shift requires operand widths"
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
      else evalSized env (.binary op l r)
  | .ternary c t e =>
      if t.isInt env && e.isInt env then do
        let cv ← evalInt env c
        if cv != 0 then evalInt env t else evalInt env e
      else evalSized env (.ternary c t e)
  | .concat _ => .error "concatenation in a constant context"
  -- A conversion at a root (round 3 folds; round 4: `evalSized` reads it
  -- as an assignment-like target, `PExpr.pushedTarget`) — the operand's
  -- own bits zero-extended (a signed operand under the
  -- `_sym_unsigned_simple_operand` marker taken modulo its own width
  -- first: `-3` is `2^32 - 3`), never truncated to the default point's
  -- width (the caller converts to its target), loud where the target's
  -- reading differs (a genvar initializer, `_sym_genvar_init`).
  | .resize w a => evalSized env (.resize w a)
  -- A sign extension (extractor `_sym_signed_widening`, `SB + 5` with a
  -- `byte` SB): width-exact.
  | .signedResize w a => evalSized env (.signedResize w a)
  | .squash2 _ a => evalInt env a
  | .sysCall fn a =>
      match fn, a with
      | .clog2, e => do
          let v ← evalInt env e
          if v < 0 then .error "$clog2 of a negative value" else .ok (clog2 v.toNat : Int)
      | .bits, .ident n =>
          match env.widths.lookup n with
          | some w => .ok (w : Int)
          | none => .error s!"$bits/$size of undeclared signal '{n}'"
      | .size, .ident n => dimQuery env "$size" n false
      | .high, .ident n => dimQuery env "$high" n true
      | f, _ => .error s!"{f.sym} argument outside the declared-signal tier"
  | .bitSel base idx =>
      if base.isInt env then do
        let v ← evalInt env base
        let i ← evalInt env idx
        if v < 0 then .error "bit select of a negative constant (width-dependent)"
        else if i < 0 || 32 ≤ i then .error "constant bit select out of range (reads x)"
        else .ok (Int.ofNat ((v.toNat >>> i.toNat) % 2))
      else evalSized env (.bitSel base idx)
  | .partSel base msb lsb =>
      if base.isInt env then do
        let v ← evalInt env base
        let m ← evalInt env msb
        let l ← evalInt env lsb
        if v < 0 then .error "part select of a negative constant (width-dependent)"
        else if l < 0 || m < l || 32 ≤ m then .error "bad part-select bounds"
        else .ok (Int.ofNat ((v.toNat >>> l.toNat) % 2 ^ (m - l + 1).toNat))
      else evalSized env (.partSel base msb lsb)
  | .repl _ _ => .error "replication in a constant context"
  | .reduce _ _ => .error "reduction in a constant context (width-dependent)"
  | .cast s a => if s && a.isInt env then evalInt env a else evalSized env (.cast s a)
  | .arrayElem n _ | .arrayPart n .. => .error s!"signal '{n}' in a constant context"
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

@[simp] theorem maxW_some (left right : Nat) :
    maxW (some left) (some right) = some (max left right) := rfl

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
      | .m0 .wildEq | .m0 .wildNe
      | .m0 .slt | .m0 .sle | .m0 .sgt | .m0 .sge
      | .slt | .sle | .sgt | .sge | .ceq | .cne | .land | .lor => some 1
      | .shl | .shr | .ashl | .ashr | .pow => selfWidth env l
      | .m0 (.pow ..) | .m0 (.shl ..) | .m0 (.shr ..)
      | .m0 (.ashl ..) | .m0 (.ashr ..) => divOperandWidth env l
      | .m0 .div | .m0 .sdiv | .m0 .rem | .m0 .srem | .div | .mod =>
          maxW (divOperandWidth env l) (divOperandWidth env r)
      | _ => maxW (selfWidth env l) (selfWidth env r)
  | .ternary _ t e => maxW (selfWidth env t) (selfWidth env e)
  | .concat parts => selfWidthSum env parts
  | .resize w _ | .signedResize w _ => some w
  | .squash2 w _ => some w
  -- Semantic-tier nodes: the M0 layer does not know element widths
  -- (`Param2.lean`'s `selfWidth2` does); `none` = unknowable here.
  | .bitSel .. | .partSel .. | .repl .. | .arrayElem .. | .arrayPart .. => none
  | .reduce .. => some 1
  | .cast _ a => selfWidth env a
  | .unsupported .. => none

def selfWidthSum (env : IEnv) : List PExpr → Option Nat
  | [] => some 0
  | p :: rest =>
      match selfWidth env p, selfWidthSum env rest with
      | some a, some b => some (a + b)
      | _, _ => none

def divOperandWidth (env : IEnv) : PExpr → Option Nat
  | .resize _ operand | .signedResize _ operand => divOperandWidth env operand
  | .lit value => some value.width
  | .ident name => env.widths.lookup name
  | .paramRef name _ => some ((env.pwidths.lookup name).getD 32)
  | .genvarRef _ | .int _ | .sysCall .. => some 32
  | .enumRef name _ _ => env.enums.lookup name
  | .fill _ => none
  | .unary (.m0 .lnot) _ => some 1
  | .unary (.m0 _) operand | .unary .plus operand => divOperandWidth env operand
  | .unary _ _ => none
  | .binary operator left right =>
      match operator with
      | .m0 .eq | .m0 .ne | .m0 .wildEq | .m0 .wildNe
      | .m0 .lt | .m0 .le | .m0 .gt | .m0 .ge
      | .m0 .slt | .m0 .sle | .m0 .sgt | .m0 .sge
      | .slt | .sle | .sgt | .sge | .ceq | .cne | .land | .lor => some 1
      | .shl | .shr | .ashl | .ashr | .pow => divOperandWidth env left
      | .m0 (.pow ..) | .m0 (.shl ..) | .m0 (.shr ..)
      | .m0 (.ashl ..) | .m0 (.ashr ..) => divOperandWidth env left
      | _ => maxW (divOperandWidth env left) (divOperandWidth env right)
  | .ternary _ left right => maxW (divOperandWidth env left) (divOperandWidth env right)
  | .concat parts => divOperandWidthSum env parts
  | .squash2 width _ => some width
  | .reduce .. => some 1
  | .cast _ operand => divOperandWidth env operand
  | .bitSel .. | .partSel .. | .repl .. | .arrayElem .. | .arrayPart ..
  | .unsupported .. => none

def divOperandWidthSum (env : IEnv) : List PExpr → Option Nat
  | [] => some 0
  | operand :: rest =>
      match divOperandWidth env operand, divOperandWidthSum env rest with
      | some left, some right => some (left + right)
      | _, _ => none
end

def fitDivOperand (signed : Bool) (context sourceWidth : Option Nat) (operand : Expr) : Expr :=
  match context, sourceWidth with
  | some target, some source =>
      if target == source then operand
      else if signed then .resizeSigned target operand
      else if source < target then .concat #[.lit (.replicate (target - source) .l0), operand]
      else .unsupported "Division:operand-width" s!"{source} -> {target}"
  | _, _ => operand

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
      | none =>
          match env.nvals.lookup n with
          | some (v, _, _) =>
              -- A stale constant (`IEnv.stale`, Param2's `instExpr2` twin).
              if env.stale.contains n then
                .unsupported "ParamRef:override-type" s!"'{n}': typed at its default"
              else intLit ctx v
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
      | .plus => .unary .pos (instExpr env (maxW ctx (selfWidth env a)) a)
      | .inc | .dec => .unsupported "UnaryExpression:incdec" ""
  | .binary op l r =>
      match op with
      | .m0 (.pow signedBase signedExponent) =>
          let baseContext := maxW ctx (divOperandWidth env l)
          .binary (.pow signedBase signedExponent)
            (instDivOperand env signedBase baseContext l)
            (instDivOperand env signedExponent (divOperandWidth env r) r)
      | .m0 operator@(.shl signedLeft) | .m0 operator@(.shr signedLeft)
      | .m0 operator@(.ashl signedLeft) | .m0 operator@(.ashr signedLeft) =>
          let leftContext := maxW ctx (divOperandWidth env l)
          .binary operator (instDivOperand env signedLeft leftContext l)
            (instDivOperand env false (divOperandWidth env r) r)
      | .m0 .div | .m0 .sdiv | .m0 .rem | .m0 .srem =>
          let octx := maxW ctx (maxW (divOperandWidth env l) (divOperandWidth env r))
          .binary (match op with
            | .m0 .sdiv => .sdiv
            | .m0 .srem => .srem
            | .m0 .rem => .rem
            | _ => .div)
            (instDivOperand env (op == .m0 .sdiv || op == .m0 .srem) octx l)
            (instDivOperand env (op == .m0 .sdiv || op == .m0 .srem) octx r)
      | .m0 .add | .m0 .sub | .m0 .and | .m0 .or | .m0 .xor =>
          let octx := match ctx with
            | some w => some w
            | none => maxW (selfWidth env l) (selfWidth env r)
          .binary (match op with
              | .m0 bop => bop
              | _ => .add)  -- unreachable: this arm only matches `.m0`
            (instExpr env octx l) (instExpr env octx r)
      | .m0 .eq | .m0 .ne | .m0 .wildEq | .m0 .wildNe
      | .m0 .lt | .m0 .le | .m0 .gt | .m0 .ge
      | .m0 .slt | .m0 .sle | .m0 .sgt | .m0 .sge =>
          let octx := maxW (selfWidth env l) (selfWidth env r)
          .binary (match op with
              | .m0 bop => bop
              | _ => .eq)  -- unreachable
            (instExpr env octx l) (instExpr env octx r)
      | .land | .lor =>
          .binary (if op == .land then .land else .lor)
            (instExpr env (selfWidth env l) l)
            (instExpr env (selfWidth env r) r)
      | _ =>
          match evalInt env (.binary op l r) with
          | .ok v => intLit ctx v
          | .error e =>
              match op with
              | .m0 .mul | .mul =>
                  let octx := maxW ctx (maxW (selfWidth env l) (selfWidth env r))
                  .binary .mul (instExpr env octx l) (instExpr env octx r)
              | _ => .unsupported s!"BinaryExpression:{op.sym}" e
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
  | .signedResize width operand =>
      .resizeSigned (ctx.getD width) (instExpr env (selfWidth env operand) operand)
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
  -- A signed literal (`4'sd3`: `Ingest2` reads it as `cast true (lit)`) is
  -- its bits; signedness acts through the operators the extractor spelled.
  | .cast _ (.lit v) => .lit v
  | .cast .. => .unsupported "T2:Cast" "cast outside the M0 tier"
  | .arrayElem .. | .arrayPart .. =>
      .unsupported "T2:ArraySel" "packed-array select path outside the M0 tier"
  | .unsupported k t => .unsupported k t

/-- Concat parts: each part is self-determined (an inner fill with no
self width is loud — the LRM agrees: unsized literals are illegal in
concats). -/
def instParts (env : IEnv) : List PExpr → List Expr
  | [] => []
  | p :: rest => instExpr env (selfWidth env p) p :: instParts env rest

def instDivOperand (env : IEnv) (signed : Bool) (ctx : Option Nat) : PExpr → Expr
  | .unary (.m0 .lnot) operand =>
      fitDivOperand signed ctx (some 1)
        (.unary .lnot (instDivOperand env false (divOperandWidth env operand) operand))
  | .unary (.m0 operator) operand =>
      .unary operator (instDivOperand env signed (maxW ctx (divOperandWidth env operand)) operand)
  | .unary .plus operand =>
      .unary .pos (instDivOperand env signed (maxW ctx (divOperandWidth env operand)) operand)
  | .binary (.m0 (.pow _ signedExponent)) left right =>
      .binary (.pow signed signedExponent)
        (instDivOperand env signed (maxW ctx (divOperandWidth env left)) left)
        (instDivOperand env signedExponent (divOperandWidth env right) right)
  | .binary (.m0 operator@(.shl _)) left right
  | .binary (.m0 operator@(.shr _)) left right
  | .binary (.m0 operator@(.ashl _)) left right
  | .binary (.m0 operator@(.ashr _)) left right =>
      let shifted := match operator with | .ashr _ => .ashr signed | _ => operator
      .binary shifted
        (instDivOperand env signed (maxW ctx (divOperandWidth env left)) left)
        (instDivOperand env false (divOperandWidth env right) right)
  | .binary (.m0 operator) left right =>
      let own := maxW (divOperandWidth env left) (divOperandWidth env right)
      let comparison := match operator with
        | .eq | .ne | .wildEq | .wildNe | .lt | .le | .gt | .ge => true
        | _ => false
      let common := if comparison then own else maxW ctx own
      let value := Expr.binary operator
        (instDivOperand env signed common left) (instDivOperand env signed common right)
      if comparison then fitDivOperand signed ctx (some 1) value else value
  | .binary .mul left right =>
      let common := maxW ctx (maxW (divOperandWidth env left) (divOperandWidth env right))
      .binary .mul (instDivOperand env signed common left) (instDivOperand env signed common right)
  | .resize width operand => instDivOperand env false (ctx.orElse (fun _ => some width)) operand
  | .signedResize width operand => instDivOperand env true (ctx.orElse (fun _ => some width)) operand
  | .ternary condition left right =>
      let common := maxW ctx (maxW (divOperandWidth env left) (divOperandWidth env right))
      .ternary (instDivOperand env false (divOperandWidth env condition) condition)
        (instDivOperand env signed common left) (instDivOperand env signed common right)
  | .concat parts =>
      fitDivOperand signed ctx (divOperandWidthSum env parts)
        (.concat (instDivParts env parts).toArray)
  | operand =>
      let source := divOperandWidth env operand
      fitDivOperand signed ctx source (instExpr env (source.orElse (fun _ => ctx)) operand)

def instDivParts (env : IEnv) : List PExpr → List Expr
  | [] => []
  | operand :: rest =>
      instDivOperand env false (divOperandWidth env operand) operand :: instDivParts env rest
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
          .ok { name := pd.name, width := w, isSigned := pd.isSigned,
                twoState := pd.twoState,
                isInput := pd.isInput, isOutput := pd.isOutput }
      | some ie =>
          match instExpr env (some w) ie with
          | .lit v =>
              .ok { name := pd.name, width := w, isSigned := pd.isSigned,
                    twoState := pd.twoState,
                    isInput := pd.isInput, isOutput := pd.isOutput, init := some v }
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

/-- Whether every declared bound of a type is a literal, so that its width
is the same at every parameter point (round 5 folds, `declConstType`). -/
def PType.boundsLiteral : PType → Bool
  | .packed ds _ => ds.all fun d =>
      (match d.msb with | .int _ | .lit _ => true | _ => false) &&
      (match d.lsb with | .int _ | .lit _ => true | _ => false)
  | _ => true

/-- The constant-tier type of a declared parameter/localparam type:
`none` = the INT class (no type, or a 32-bit signed type — `int`,
`integer`), `some (w, s)` otherwise. `signed?` is the envelope's `signed`
field; absent, a type is signed exactly when it is 32 bits wide (the
extractor emits the field for every type departing from that default:
`int unsigned`, `logic [31:0]`, `byte`, …) — a rule about ONE width, so a
type with a non-literal bound (`logic signed [M-1:0]`) without the field is
loud (round 5 folds; the extractor always emits it for such a type). -/
def declConstType (env : IEnv) (ty? : Option PType) (signed? : Option Bool) :
    Except String (Option (Nat × Bool)) :=
  match ty? with
  -- No type and no range: the type of the final value — an integer override
  -- is an `int` (§6.20.2), unless an explicit `unsigned` keyword makes it
  -- 32-bit unsigned. (The default point is `PDesign.atPoint`'s.)
  | none => .ok (if signed? == some false then some (32, false) else none)
  -- An enum-typed parameter holds a member value; enum tables bind after the
  -- parameters (`bindEnums`), so it keeps the INT reading it always had.
  | some (.typeRef ..) => .ok none
  | some ty => do
      let w ← ty.width env
      let s ← match signed? with
        | some s => pure s
        | none =>
            -- Round 5 folds (verifier repros `vq_sgn2`, `vq_sgn3`): the
            -- default rule is a fact of ONE width; a type whose width
            -- depends on a parameter must say (the extractor always emits
            -- the field for one, `_sym_param_signedness`).
            if ty.boundsLiteral then pure (w == 32)
            else throw "a parameter-dependent type without its declared signedness (envelope `signed`): the default rule (signed exactly when 32 bits wide) would be read at this point's width"
      .ok (if w == 32 && s then none else some (w, s))

/-- A literal dimension bound (`PDim` as the extractor writes `[7:4]`). -/
def PExpr.isLitBound : PExpr → Bool
  | .int _ | .lit _ => true
  | _ => false

/-- `IEnv.pdims` after binding the typed constant `n` of type `ty?`: its
evaluated range when some declared bound is not a literal (round 3 folds,
`paramSelectOk`); `env` unchanged otherwise (literal bounds, a `typeRef`,
no type, or bounds that do not evaluate — the width computation that
typed the constant has already reported those). -/
def IEnv.withPDims (env : IEnv) (n : String) (ty? : Option PType) : IEnv :=
  match ty? with
  | some (.packed ds _) =>
      if ds.all (fun d => d.msb.isLitBound && d.lsb.isLitBound) then env
      else
        match ds.mapM (fun d => do pure ((← evalInt env d.msb), (← evalInt env d.lsb))) with
        | .ok es => { env with pdims := (n, es) :: env.pdims }
        | .error _ => env
  | _ => env

/-- Bind module parameters to their argument values in declaration order
(each type sees the earlier parameters): INT-class parameters append to
`vals` (so a parameter list of INT parameters binds exactly
`(names).zip args`), every other typed parameter goes to `nvals` with its
value converted to the declared type (`canonInt` — what SV does with an
override that does not fit). -/
def bindParams (env : IEnv) : List PParam → List Int → Except String IEnv
  | p :: ps, v :: vs => do
      match ← (declConstType env p.type? p.signed?).mapError
          (fun e => s!"parameter '{p.name}' type: {e}") with
      | none =>
          if p.overrideRetypes then
            bindParams { env.bindNVal p.name (canonInt 32 true v) 32 true with
              stale := p.name :: env.stale } ps vs
          else if env.int32 then
            bindParams (env.bindNVal p.name (canonInt 32 true v) 32 true) ps vs
          else bindParams { env with vals := env.vals ++ [(p.name, v)] } ps vs
      | some (w, s) =>
          if p.overrideRetypes then
            bindParams { (env.withPDims p.name p.type?).bindNVal p.name (canonInt w s v) w s with
              stale := p.name :: env.stale } ps vs
          else bindParams ((env.withPDims p.name p.type?).bindNVal p.name (canonInt w s v) w s) ps vs
  | _, _ => .ok env

/-- `bindParams` in `Res` (a failure is a loud `.unsupported`). -/
def bindParamsRes (env : IEnv) (ps : List PParam) (args : List Int) : Res IEnv :=
  match bindParams env ps args with
  | .ok e => .ok e
  | .error e => .unsupported e

/-! ### §6.20.2 at the default point

`instantiate`/`instantiate2` read every argument as an integer OVERRIDE
(`#(.P(5))`), and an untyped parameter takes the type of its FINAL value
(IEEE 1800-2023 §6.20.2) — at an overridden point that is the override's
type, an `int`, which is what `bindParams` binds. At a point where the
parameter is NOT overridden its final value is its default, so its type is
the default expression's: `parameter P = 3'd5` is 3-bit unsigned there and
`v[P + 3'd4 +: 2]` wraps to `v[2:1]` in every simulator (verifier finding
2026-10-28). `PDesign.atPoint` models such a point by RETYPING the
not-overridden parameters (`PParam.retype`) before instantiation; the
load-time gate (`crossCheck`) and the differential runner instantiate
through it. -/

/-- `e` with every shift (`<< >> <<< >>>`) on its context-propagation chain
read at its OWN type (a `.cast` of its own signedness): the wide reading of
`evalUntyped` (round 5). Icarus 12.0's lossless evaluation of an untyped
parameter value stops at a shift (measured: `(SB + 1'b1) >> 1`, `(SB +
1'b1) << 1`, `SB << 4` and `(SB * SB) >> 8` keep their own 8 bits there,
while `+ - * / **`, unary `-` and the arms of `?:` widen), and
comparisons, logical operators, casts and selects are self-determined in
`evalAt` already. Round 7 folds: that holds for a RIGHT shift and for a
SIZED left operand only; a LEFT shift whose left operand is or contains an
unsized or INT-class operand widens in Icarus (`1 << N` is 32 + N bits,
2^40 at `N = 40`), so `PExpr.icarusWidens` refuses every left shift before
`evalUntyped` reaches this reading. -/
def PExpr.shiftBarriers (env : IEnv) : PExpr → PExpr
  | .unary op a => .unary op (a.shiftBarriers env)
  | .binary op l r =>
      match op with
      | .shl | .shr | .ashl | .ashr =>
          match ctype env l with
          | .ok (_, s) => .cast s (.binary op l r)
          | .error _ => .binary op l r
      | .pow => .binary op (l.shiftBarriers env) r
      | _ =>
          match op.constClass with
          | .arith => .binary op (l.shiftBarriers env) (r.shiftBarriers env)
          | _ => .binary op l r
  | .ternary c t e => .ternary c (t.shiftBarriers env) (e.shiftBarriers env)
  | .resize w a => .resize w (a.shiftBarriers env)
  | .signedResize w a => .signedResize w (a.shiftBarriers env)
  | .squash2 w a => .squash2 w (a.shiftBarriers env)
  | e => e

/-- The refusal of an untyped constant whose self-determined value wraps
(`evalUntyped`). -/
def untypedWrapMsg (w : Nat) (v v' : Int) : String :=
  s!"Constant:untyped-overflow — an untyped parameter or localparam takes its expression's own type (IEEE 1800-2023 §6.20.2), {w} bits here, where its value is {v}; evaluated without that bound it is {v'}: slang, the LRM and Yosys 0.53 keep the {w}-bit value, Icarus 12.0 evaluates an untyped parameter value losslessly (measured: `SB + 1'b1` with an 8-bit SB = 255 is 0 against 256) — refused where the readings differ"

/-- **Whether Icarus 12.0 can give an untyped constant a WIDER type than its
own** (round 6 folds, round 5 FOLDS verifier major 3 and minor 4).
IEEE 1800-2023 §6.20.2 types an untyped parameter or localparam by its
expression (slang, Yosys 0.53: `$bits` of `SB + 1'b1` with an 8-bit `SB`
is 8, of `N + 1` with an `int N` 32); Icarus 12.0, in its default
`-gno-strict-expr-width` mode, gives it the LOSSLESS width of that
expression (measured with `$bits`, scratch `gaps5/folds/p/uw`): one carry
bit per `+` and `-` (`SB + 1'b1` 9, `N + 1` and `5 + 1` 33, `SB + 8'd0 -
8'd0` 10), the operand widths summed for `*` (`SB * 2'd2` 10, `N * 2`
64), a base- and value-dependent width for `**` (`SB ** 2` 16, `N ** 2`
64, `2'd2 ** SB` 2, `2 ** N` 32 at `N = 8` and 42 at `N = 40`), carried
through `/ % & | ^`, unary `- ~ +` and both arms of `?:` (`(N + 1) / 2`,
`M ? N : N + 1`: 33), and stopped by a RIGHT shift, a comparison, a
cast, a select and a concatenation part (`(N + 1) >> 1` 32, `$signed(N +
1)` 32, `{SB + 1'b1}` 8). Round 7 folds (round 6 FOLDS verifier blocker
3, scratch `gaps5/vfolds/w/w3.sv`, `w4.sv`): a LEFT shift is not a
barrier — Icarus widens `<<`/`<<<` by the shift amount where the left
operand is or contains an unsized or INT-class operand (`1 << N` 40 bits
at `N = 8` and 72 at `N = 40`, where the value is 2^40 and Yosys gives 0;
`1 << 3` 35, `7 << 1` 33, `(N | 1) << 2` 34, carried through `(1 << N) |
1` and `(1 << N) / 2`), so every left shift counts as widening, a sized
left operand included (`SB << 4` stays 8 bits in Icarus — a recorded
over-refusal). A wider type is observable wherever the constant's width
is: as a concatenation part (`{a, B}` with `localparam B = N + 1`: Icarus
`0x1e00000009`, Yosys `0xf00000009` at `a = 4'hF`; `{a, E}` with
`localparam E = 2 ** N` at `N = 40`, where the 32-bit materialization made
`int32Agrees` see no difference and the model followed Yosys), as a
negative operand zero-extended into a wider unsigned context (`a + B` with
`B = N - 9 = -1` into 64 bits: `0x200000002` against `0x100000002`), and
in a context it widens (`(Y + 8'd255) >> 1` into 8 bits with `Y = SB +
1'b1`, `SB = 5`: 130 against 2). `true` over-approximates: `+ - * **`
and a left shift anywhere on the expression's context chain (`2 ** N` is
32 bits in Icarus at `N = 8` and refused too — a recorded over-refusal;
the value-position spellings `u/`, `s%`, `u**u`, `u<<` count like `/ % **
<<`). -/
def PExpr.icarusWidens (env : IEnv) : PExpr → Bool
  | .binary op l r =>
      match op with
      | .m0 .add | .m0 .sub | .m0 .mul | .mul | .pow | .m0 (.pow ..) => true
      -- Round 7 folds: a LEFT shift widens (`1 << N` is 32 + N bits).
      | .shl | .ashl | .m0 (.shl _) | .m0 (.ashl _) => true
      | .m0 .and | .m0 .or | .m0 .xor | .div | .mod
      | .m0 .div | .m0 .sdiv | .m0 .rem | .m0 .srem => l.icarusWidens env || r.icarusWidens env
      | _ => false
  | .unary (.m0 .lnot) _ => false
  | .unary _ a => a.icarusWidens env
  | .ternary _ t e => t.icarusWidens env || e.icarusWidens env
  | .resize _ a | .signedResize _ a | .squash2 _ a => a.icarusWidens env
  | _ => false

/-- The refusal of an untyped constant that Icarus 12.0 types wider than
its own type (`evalUntyped`, `PExpr.icarusWidens`). -/
def untypedWidthMsg : String :=
  s!"Constant:untyped-width — an untyped parameter or localparam takes its expression's own type (IEEE 1800-2023 §6.20.2; slang, Yosys 0.53), while Icarus 12.0 gives it the lossless width of an expression built with + - * or ** ($bits of `SB + 1'b1` with an 8-bit SB is 9, of `N + 1` with an int N 33): the two are different constants wherever the width is observable (a concatenation part, a negative value extended into a wider unsigned context, a context it widens) — refused for every such untyped constant, at every point"

/-- **The value of an UNTYPED parameter default or localparam** (round 5
folds, round 3 verifier minor 4): `evalInt` — its expression's own type
(§6.20.2) — loud where that value WRAPS, i.e. differs from its reading at
64 more bits with shifts kept at their own width (`PExpr.shiftBarriers`;
`Constant:untyped-overflow`). The tools split there: slang, the LRM and
the Yosys 0.53 netlist keep the self-determined value (`localparam Y = SB
+ 1'b1` with an 8-bit `SB = 255` is 0), Icarus 12.0 evaluates an untyped
parameter value losslessly (256; measured also `Z - 1'b1` at `Z = 0`: 511,
`SB * SB`: 65025, `(SB + 1'b1) / 2'd2`: 128, `-(SB + 1'b1)`: 256, `SS +
SS` with a signed `SS = 127`: 254, `SB[3:0] + 4'd1`: 16). The check is an
over-approximation of Icarus's widths, so it also refuses some values
Icarus happens to keep (`-SB`, `~SB`, `~(SB + 1'b1)`: unary operators on
an unsigned value read differently at every wider width) — loudly. An
INT-class expression keeps `evalInt`'s unbounded reading (32-bit `int`
overflow is `int32Agrees`'s).

Round 6 folds (round 5 FOLDS verifier major 3, minor 4): the value check
alone did not cover the split. Icarus's lossless reading changes the
constant's WIDTH even where no value wraps (`localparam Y = SB + 1'b1` at
`SB = 5` is 9 bits there, 8 in slang and Yosys: `(Y + 8'd255) >> 1` into
8 bits is 130 against 2), it reaches INT-class constants too (`N + 1` is
33 bits), and a wrap beyond 64 extra bits escaped (`2 ** SB` at `SB =
100`). Every untyped constant whose expression can widen in Icarus
(`PExpr.icarusWidens`) is now refused first, `Constant:untyped-width`, at
every point and whatever its value — a whole-class refusal that also
refuses constants whose width is never observed (dimension bounds,
generate bounds: the cv32e40p `register_file_ff` row's `NUM_TOT_WORDS`),
a recorded over-refusal. The value check stays behind it for the
expressions it admits. -/
def evalUntyped (env : IEnv) (e : PExpr) : Except String Int := do
  -- Round 6 folds: the WIDTH splits before the value does (`untypedWidthMsg`).
  if e.icarusWidens env then throw untypedWidthMsg
  let v ← evalInt env e
  if e.isInt env then .ok v
  else
    let (w, s) ← ctype env e
    let v' ← evalAt env (w + 64, s) (e.shiftBarriers env)
    if v' == v then .ok v else .error (untypedWrapMsg w v v')

/-- **The initializer of an INT-class TARGET** (round 4 folds): an
`integer` or `int` localparam, or an `integer`/`int` parameter's default — an
assignment to a 32-bit signed target (§10.8, §11.8.1). An INT-class
initializer (or one under the `Squash2` of an `int` target) keeps
`evalInt`'s unbounded reading; any other is evaluated at `max(32, its own
width)` at THESE parameters (`evalAssign`), the caller converting to the
32-bit target. Before, such an initializer went through `evalInt`, i.e. at
its own width wherever the default point's tree held no conversion to read:
`localparam integer L = U + 1'b1` with `logic [N-1:0] U = -1` (32 bits at
the default `N = 32`) was 0 at `N = 4` and `N = 8`, where Icarus 12.0 and
the Yosys 0.53 netlist give 16 and 256 (round 3 FOLDS verifier, repros
`rf_int`, `rf_ipar` — a regression of round 3's transparent `ctype`). -/
def evalIntTarget (env : IEnv) (e : PExpr) : Except String Int :=
  if e.isInt env then evalInt env e
  else
    match e with
    | .squash2 _ a => if a.isInt env then evalInt env a else evalAssign env 32 e
    | _ => evalAssign env 32 e

/-- A parameter's DEFAULT value, before its conversion to the declared type
(round 3 folds): a typed parameter's non-INT default at its declared width
at THESE parameters (`evalAssign` — `parameter logic [N-1:0] Q = 8'd200 +
8'd100` is `300` at `N = 16`, where the envelope's default-point tree was
sized to `N = 4`; an `integer`/`int` one at 32 bits, `evalIntTarget`, round
4); an untyped default by `evalInt` (its own type, §6.20.2), loud where
that value wraps (`evalUntyped`, round 5). -/
def PParam.evalDefault (env : IEnv) (p : PParam) (e : PExpr) : Except String Int :=
  match p.type? with
  | some _ =>
      if e.isInt env then evalInt env e
      else do
        match ← declConstType env p.type? p.signed? with
        | some (w, _) => evalAssign env w e
        | none =>
            -- An enum-typed parameter (`declConstType` reads it as INT) keeps
            -- `evalInt`; an `integer`/`int` one is a 32-bit target.
            match p.type? with
            | some (.typeRef ..) => evalInt env e
            | _ => evalIntTarget env e
  | none => evalUntyped env e

/-- The constant type an UNTYPED parameter (`type? = none`) has when it is
NOT overridden: its default expression's self-determined type (`ctype`),
with a declared signing keyword (`signed?` — `parameter signed P = 4'd3`)
applied; `none` when that is the INT class (32-bit signed — `bindParams`'
reading already). Typed and ranged parameters keep their declared type at
every point (`none`). -/
def PParam.defaultConstType (env : IEnv) (p : PParam) :
    Except String (Option (Nat × Bool)) :=
  match p.type?, p.default? with
  | none, some e =>
      if e.isInt env && p.signed? != some false then .ok none
      else do
        let (w, s) ← ctype env e
        let s := p.signed?.getD s
        -- The override reading (`declConstType none p.signed?`) already.
        if w == 32 && s == p.signed?.getD true then .ok none
        else .ok (some (w, s))
  | _, _ => .ok none

/-- `p` declared at the constant type `(w, s)`: a `[w-1:0]` packed type
with explicit signedness (`PDesign.atPoint`'s retyping). -/
def PParam.retype (p : PParam) (w : Nat) (s : Bool) : PParam :=
  { p with type? := some (.packed [⟨.int ((w : Int) - 1), .int 0⟩] (some w)),
           signed? := some s, overrideRetypes := false }

/-- **A partially overridden parameter point** `#(.P(v), …)`: `given[i] =
some v` overrides the i-th parameter with the integer `v`; `none` (or a
missing entry) keeps its default, evaluated in declaration order (each
default sees the earlier parameters). Returns the design with every
not-overridden untyped parameter whose default is not INT-class retyped to
the default's type (`PParam.defaultConstType`) and the argument list for
`instantiate`/`instantiate2`, defaults converted to their bound type (the
`defaultArgs` rule). At the all-default point this is the design slang
elaborated the envelope's `resolved` metadata at. -/
def PDesign.atPoint (d : PDesign) (given : List (Option Int)) :
    Except String (PDesign × List Int) := do
  let (ps, args) ← go {} d.params given
  return ({ d with params := ps }, args)
where
  go (env : IEnv) : List PParam → List (Option Int) → Except String (List PParam × List Int)
    | [], _ => .ok ([], [])
    | p :: rest, given => do
        let g := given.head?.join
        let (p', v) ← match g with
          | some v => pure (p, v)
          | none =>
              match p.default? with
              | none => throw s!"parameter '{p.name}' has no default"
              | some e => do
                  let v ← (p.evalDefault env e).mapError fun m => s!"parameter '{p.name}' default: {m}"
                  match ← (p.defaultConstType env).mapError
                      (fun m => s!"parameter '{p.name}' default type: {m}") with
                  | none => pure (p, v)
                  | some (w, s) => pure (p.retype w s, v)
        let env' ← bindParams env [p'] [v]
        let v' := match g, env'.nvals.lookup p'.name with
          | none, some (c, _, _) => c
          | _, _ => v
        let (ps, vs) ← go env' rest given.tail
        .ok (p' :: ps, v' :: vs)

/-- Set `PParam.overrideRetypes` on exactly the parameters `atPoint []`
retypes — the untyped ones whose default-point type is not their override
reading. Ingestion (`Ingest2`) applies it to every loaded envelope; a design
whose defaults fail to evaluate is left unmarked (the load gate refuses it). -/
def PDesign.markOverrideRetypes (d : PDesign) : PDesign :=
  match d.atPoint [] with
  | .ok (d', _) =>
      { d with params := (d.params.zip d'.params).map fun (p, p') =>
          { p with overrideRetypes := p.type?.isNone && p'.type?.isSome } }
  | .error _ => d

/-- Bind one localparam: a typed one takes its declared type (the value
converted to it — the assignment-like context of §10.8, evaluated at the
declared width at THESE parameters by `evalAssign`: slang sized the tree
to the DEFAULT point's width only); an untyped one takes the type of its
expression (INT class to `vals`, anything else to `nvals` at its `ctype`). -/
def bindLocal (env : IEnv) (lp : PLocalParam) : Except String IEnv := do
  match lp.type? with
  | none =>
      -- Round 5 folds: loud where its own-type value wraps (`evalUntyped`).
      let v ← evalUntyped env lp.expr
      if lp.expr.isInt env then .ok (env.bindVal lp.name v)
      else
        let (w, s) ← ctype env lp.expr
        -- Its type is its expression's, so it is stale where that reads one.
        let env' := env.bindNVal lp.name v w s
        .ok (if !env.stale.isEmpty && lp.expr.mentionsAny env.stale then
          { env' with stale := lp.name :: env.stale } else env')
  | some ty =>
      match ← declConstType env lp.type? lp.signed? with
      | none =>
          -- Round 4 folds: an `integer`/`int` localparam is a 32-bit target
          -- (`evalIntTarget`, repro `rf_int`); an enum-typed one keeps `evalInt`.
          let v ← match ty with
            | .typeRef .. => evalInt env lp.expr
            | _ => evalIntTarget env lp.expr
          if env.int32 then .ok (env.bindNVal lp.name (canonInt 32 true v) 32 true)
          else .ok (env.bindVal lp.name (if lp.expr.isInt env then v else canonInt 32 true v))
      | some (w, s) =>
          -- Round 3 folds: the initializer at the declared width HERE
          -- (`evalAssign`), not the default point's (`vp_lp2`, `vp_lp`).
          let v' ← if lp.expr.isInt env then evalInt env lp.expr else evalAssign env w lp.expr
          .ok ((env.withPDims lp.name lp.type?).bindNVal lp.name (canonInt w s v') w s)

/-- Bind localparams in declaration order (each sees the parameters and
all earlier localparams). -/
def bindLocals (env : IEnv) : List PLocalParam → Res IEnv
  | [] => .ok env
  | lp :: rest =>
      match bindLocal env lp with
      | .error e => .unsupported s!"localparam '{lp.name}': {e}"
      | .ok env' => bindLocals env' rest

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
  | .inst i => .ok [.unsupported "Instance"
      s!"module instance '{i.name}' of '{i.module}' outside the M0 tier"]
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
    let env0 ← bindParamsRes {} d.params args
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
            match p.evalDefault env e with
            | .error err => .unsupported s!"parameter '{p.name}' default: {err}"
            | .ok v =>
                -- The default converted to the declared type, bound the way
                -- `instantiate` binds it (later defaults see the same class).
                match bindParams env [p] [v] with
                | .error err => .unsupported err
                | .ok env' => do
                    let v' := match env'.nvals.lookup p.name with
                      | some (c, _, _) => c
                      | none => v
                    let vs ← go env' rest
                    .ok (v' :: vs)

private def checkLocals (env : IEnv) : List PLocalParam → List String × IEnv
  | [] => ([], env)
  | lp :: rest =>
      match bindLocal env lp with
      | .error e => ([s!"localparam '{lp.name}': {e}"], env)
      | .ok env' =>
          let v := match env'.vals.lookup lp.name, env'.nvals.lookup lp.name with
            | some x, _ => x
            | none, some (x, _, _) => x
            | none, none => 0
          let tail := checkLocals env' rest
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
def PDesign.crossCheck (d₀ : PDesign) : List String :=
  -- The DEFAULT point (`atPoint []`): untyped parameters with a non-INT
  -- default carry the default's type, as in slang's elaboration.
  match d₀.atPoint [] with
  | .error e => [s!"defaults: {e}"]
  | .ok (d, args) =>
      let paramMsgs := (d.params.zip args).filterMap fun (p, v) =>
        match p.resolved? with
        | some r => if r == v then none else some s!"parameter '{p.name}': ours {v} ≠ resolved {r}"
        | none => none
      let env0 : IEnv := (bindParams {} d.params args).toOption.getD {}
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
    obtain ⟨_, _, env1, _, env2, _, decls, hdecls, gens, _, hm⟩ := h
    cases hm
    simpa [PDesign.declSig] using buildDecls_sig hdecls

/-- The instantiated design's name is the source module name. -/
theorem instantiate_name {d : PDesign} {args : List Int} {F : Nat} {m : Design}
    (h : d.instantiate args F = .ok m) : m.name = d.name := by
  unfold PDesign.instantiate at h
  split at h
  · exact absurd h (by simp)
  · simp only [Res.bind_eq_ok] at h
    obtain ⟨_, _, _, _, _, _, _, _, _, _, hm⟩ := h
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

/-- Signed `<` on evaluated INT-class operands (the canonical generate-loop
bound shape). -/
theorem evalInt_slt {env : IEnv} {l r : PExpr} {a b : Int}
    (hil : l.isInt env = true) (hir : r.isInt env = true)
    (hl : evalInt env l = .ok a) (hr : evalInt env r = .ok b) :
    evalInt env (.binary .slt l r) = .ok (b2i (decide (a < b))) := by
  simp only [evalInt, hil, hir, Bool.and_self, if_true, hl, hr]
  rfl

/-- The genvar sequence of the canonical ascending loop
(`for (g = i0; g s< e; g++)` with a loop-invariant bound expression
`e ⇓ N`): consecutive integers `i0, i0+1, …, N-1`, provided the fuel
exceeds the trip count. **The** induction workhorse for `ff_one`-shaped
∀-parameter families. -/
theorem genvarSeq_ascending {env : IEnv} {g : String} {e : PExpr} {N : Int}
    (hei : ∀ i : Int, e.isInt (env.bindVal g i) = true)
    (he : ∀ i : Int, evalInt (env.bindVal g i) e = .ok N) :
    ∀ {fuel : Nat} (i0 : Int), (N - i0).toNat < fuel →
      genvarSeq env g (.binary .slt (.genvarRef g) e) 1 fuel i0 =
        .ok (intRange i0 (N - i0).toNat) := by
  intro fuel
  induction fuel with
  | zero => intro i0 h; omega
  | succ fuel ih =>
      intro i0 hfuel
      have hbound := evalInt_slt (env := env.bindVal g i0) (l := .genvarRef g) rfl (hei i0)
        (evalInt_genvarRef_bind (env := env) (g := g) (v := i0)) (he i0)
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
    (hei : ∀ i : Int, e.isInt (env.bindVal g i) = true)
    (he : ∀ i : Int, evalInt (env.bindVal g i) e = .ok N)
    {fuel : Nat} {i0 : Int} (hfuel : (N - i0).toNat < fuel) {vs : List Int}
    (h : genvarSeq env g (.binary .slt (.genvarRef g) e) 1 fuel i0 = .ok vs) :
    vs.length = (N - i0).toNat := by
  rw [genvarSeq_ascending hei he i0 hfuel] at h
  cases h; simp

/-! ## Hand-built parametric smoke

`gen_sel(W, K)`: `W`-bit input `a`, output `y`; a generate-for over
`j s< K` whose body is a generate-if selecting exactly the last
iteration (`j == K-1`, via a localparam) to drive `assign y = a + j` —
exercising symbolic widths, localparam evaluation, `GenerateFor` +
`GenerateIf` expansion, and a genvar in a value position, all fully
inside the M0 tier after instantiation. The localparam is `localparam int
KM1 = K - 1`: since round 6 an UNTYPED `localparam KM1 = K - 1` is loud at
every point (`Constant:untyped-width`, `PExpr.icarusWidens` — Icarus 12.0
gives it 33 bits; a recorded over-refusal here, where only its value is
read), pinned below. -/

private def wm1 : PDim := ⟨.binary (.m0 .sub) (.paramRef "W" none) (.int 1), .int 0⟩

private def km1Expr : PExpr := .binary (.m0 .sub) (.paramRef "K" none) (.int 1)

private def pGenSel : PDesign :=
  { name := "gen_sel"
    params := [
      { name := "W", default? := some (.int 8), resolved? := some 8 },
      { name := "K", default? := some (.int 3), resolved? := some 3 }]
    localParams := [
      { name := "KM1", expr := km1Expr, resolved? := some 2,
        type? := some (.packed [⟨.int 31, .int 0⟩] (some 32)) }]
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
-- The untyped twin `localparam KM1 = K - 1` is loud (round 6 over-refusal).
#guard (pGenSel.instantiate [8, 3] matches .ok _)
#guard ({ pGenSel with localParams := [{ name := "KM1", expr := km1Expr, resolved? := some 2 }] }
  |>.instantiate [8, 3]) matches .unsupported _

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
  have hei : ∀ i : Int,
      (PExpr.paramRef "K" none).isInt (IEnv.bindVal { vals := [("K", (K : Int))] } "j" i) := by
    intro i
    simp [PExpr.isInt, IEnv.bindVal, List.lookup]
  have h := genvarSeq_ascending hei he (fuel := K + 1) 0 (by omega)
  simpa using h


/-! ## Width-exact constants (verifier probes `ps_wrap`/`pc`, 2026-10-28)

`logic [2:0] K` binds in `nvals`; arithmetic with sized operands wraps at the
self-determined width (IEEE 1800-2023 §11.6/§11.8) exactly as Icarus 12.0 and
Yosys 0.53 compute it; the INT path is untouched. -/

private def okIs (r : Except String Int) (v : Int) : Bool :=
  match r with
  | .ok x => x == v
  | .error _ => false

private def isLoud (r : Except String Int) : Bool :=
  match r with
  | .ok _ => false
  | .error _ => true

/-- `parameter logic [2:0] K = k`, `parameter int unsigned UI = u`,
`parameter int N = n` (an INT parameter, `vals`). -/
private def wrapEnv (k u n : Int) : IEnv :=
  { vals := [("N", n)], nvals := [("K", (k, 3, false)), ("UI", (u, 32, false))] }

private def kRef : PExpr := .paramRef "K" none
private def lit3 (v : Nat) : PExpr := .lit (.ofNat 3 v)

-- `K + 3'd4` / `K - 3'd6` wrap at 3 bits (K = 5: 1 and 7; K = 7: 3).
#guard okIs (evalInt (wrapEnv 5 0 0) (.binary (.m0 .add) kRef (lit3 4))) 1
#guard okIs (evalInt (wrapEnv 5 0 0) (.binary (.m0 .sub) kRef (lit3 6))) 7
#guard okIs (evalInt (wrapEnv 7 0 0) (.binary (.m0 .add) kRef (lit3 4))) 3
#guard okIs (evalInt (wrapEnv 1 0 0) (.binary (.m0 .sub) kRef (lit3 6))) 3
-- The extractor's `K + 1` is `Resize32(K) + 1`: 32-bit unsigned, no 3-bit wrap…
#guard okIs (evalInt (wrapEnv 7 0 0) (.binary (.m0 .add) (.resize 32 kRef) (.int 1))) 8
-- …and `U - 1` at `U = 0` is 2^32 - 1, not -1 (unsigned 32-bit; the select
-- layer refuses such a label — Icarus and Yosys read it differently).
#guard okIs (evalInt (wrapEnv 0 0 0) (.binary (.m0 .sub) (.resize 32 kRef) (.int 1))) 4294967295
-- `int unsigned UI`: `UI - 1` at 0 is 2^32 - 1 as well.
#guard okIs (evalInt (wrapEnv 0 0 0) (.binary (.m0 .sub) (.paramRef "UI" none) (.int 1))) 4294967295
-- A comparison sizes its operands to each other: `K + 3'd4 > 3'd2` at K = 5
-- compares 1 > 2 (3-bit), the generate-if of probe `ps_wrap2`.
#guard okIs (evalInt (wrapEnv 5 0 0)
  (.binary (.m0 .gt) (.binary (.m0 .add) kRef (lit3 4)) (lit3 2))) 0
-- Bit/part selects of a narrow constant read inside its width only.
#guard okIs (evalInt (wrapEnv 5 0 0) (.bitSel kRef (.int 2))) 1
#guard isLoud (evalInt (wrapEnv 5 0 0) (.bitSel kRef (.int 3)))
#guard okIs (evalInt (wrapEnv 5 0 0) (.partSel kRef (.int 2) (.int 1))) 2
-- `$signed(K)` reinterprets: K = 5 is -3.
#guard okIs (evalInt (wrapEnv 5 0 0) (.cast true kRef)) (-3)
-- A frontend `s<` over an operand typed unsigned is a contradiction: loud.
#guard isLoud (evalInt (wrapEnv 5 0 0) (.binary .slt kRef (lit3 2)))
-- Division by zero reads x: loud.
#guard isLoud (evalInt (wrapEnv 5 0 0) (.binary .div kRef (lit3 0)))
-- The INT path is unchanged: `N - 1` at N = 0 is -1 (32-bit signed).
#guard okIs (evalInt (wrapEnv 0 0 0) (.binary (.m0 .sub) (.paramRef "N" none) (.int 1))) (-1)
#guard (PExpr.binary (.m0 .sub) (.paramRef "N" none) (.int 1)).isInt (wrapEnv 0 0 0)
#guard !(PExpr.binary (.m0 .sub) kRef (.int 1)).isInt (wrapEnv 0 0 0)
-- Typed parameters bind by class: `int` → `vals`, `logic [2:0]` → `nvals`
-- (an override that does not fit is converted: 9 ↦ 1).
private def wrapParams : List PParam :=
  [{ name := "N", type? := some (.packed [⟨.int 31, .int 0⟩] none) },
   { name := "K", type? := some (.packed [⟨.int 2, .int 0⟩] none) },
   { name := "U", type? := some (.packed [⟨.int 31, .int 0⟩] none), signed? := some false }]
#guard (match bindParams {} wrapParams [4, 9, 7] with
  | .ok e => e.vals == [("N", 4)] && e.nvals == [("U", (7, 32, false)), ("K", (1, 3, false))]
  | .error _ => false)
-- Localparams: typed `logic [2:0] L = K + 3'd7` wraps (K = 1 → 0); untyped
-- `L = K + 3'd7` has the expression's own 3-bit type in slang and Yosys
-- 0.53 and a 4-bit one in Icarus 12.0: loud at every K since round 6
-- (`Constant:untyped-width`; round 5 refused only where it wraps, K = 1).
private def lpTyped : PLocalParam :=
  { name := "L", expr := .binary (.m0 .add) kRef (lit3 7),
    type? := some (.packed [⟨.int 2, .int 0⟩] none) }
private def lpUntyped : PLocalParam :=
  { name := "L", expr := .binary (.m0 .add) kRef (lit3 7) }
#guard (match bindLocal (wrapEnv 1 0 0) lpTyped with
  | .ok e => e.nvals.lookup "L" == some (0, 3, false)
  | .error _ => false)
#guard (bindLocal (wrapEnv 0 0 0) lpUntyped matches .error _)
#guard (bindLocal (wrapEnv 1 0 0) lpUntyped matches .error _)

/-! ### Constant contexts across parameter points (round 3 repair)

Conversions are transparent to `ctype` (their envelope width is the default
point's); an assignment-like target is supplied by `evalAssign` (and
`evalIntTarget` for an `integer`/`int` one, round 4); a self-determined
root is read at its own width; a root whose tree records an outside target
(`PExpr.pushedTarget`) is loud where that target's reading differs (round
4). Repros `vp_lp2`, `vp_lp`, `fold_lpshr`, `fold_cgrow`, `fold_ovr`,
`rf_lbl`, `rf_int`, `rf_gv`. -/

private def lit8 (v : Nat) : PExpr := .lit (.ofNat 8 v)
-- `localparam logic [N-1:0] L1 = 8'd200 + 8'd100`, sized at N = 4 by slang
-- (`Resize(4, …)`): the carry survives at N = 16, wraps at N = 8.
private def l1 : PExpr := .resize 4 (.binary (.m0 .add) (lit8 200) (lit8 100))
#guard okIs (evalAssign {} 16 l1) 300
#guard okIs (evalAssign {} 8 l1) 44
#guard okIs (evalAssign {} 4 l1) 44   -- the caller's `canonInt 4` makes it 12
-- `4'd15 << 2` keeps its high bits at a wider target.
#guard okIs (evalAssign {} 16 (.binary .shl (.lit (.ofNat 4 15)) (.int 2))) 60
#guard okIs (evalAssign {} 4 (.binary .shl (.lit (.ofNat 4 15)) (.int 2))) 12
-- `P + 1'b0` (`int P = -3`) into a 40-bit target: P zero-extended past 32.
#guard okIs (evalAssign { vals := [("P", -3)] } 40
  (.resize 8 (.binary (.m0 .add) (.resize 32 (.paramRef "P" none))
    (.resize 32 (.lit (.ofNat 1 0)))))) 4294967293
-- Widened literals are read at their own width where the context is
-- narrower than at the default point (N = 16 there, 8 here): 44 >> 5 = 1.
#guard okIs (evalAssign {} 8 (.binary .shr
  (.binary (.m0 .add) (.resize 16 (lit8 200)) (.resize 16 (lit8 100))) (.int 5))) 1
-- Round 4: a chain of widened non-INT leaves is NO evidence of an outside
-- target (the widths are the default point's widest operand: `SB + 1'b1`
-- is `Resize(8, SB) + Resize(8, 1'b1)` at `N = 8`) — read at its own width
-- here, 44 (repros `rf_lbl`, `rf_gen`, `rf_lp`, `rf_par`)…
#guard okIs (evalInt { nvals := [("U", (200, 8, false))] }
  (.binary (.m0 .add) (.resize 16 (.paramRef "U" none)) (.resize 16 (lit8 100)))) 44
#guard okIs (evalInt { nvals := [("SB", (-1, 4, true))] }
  (.binary (.m0 .add) (.resize 8 (.paramRef "SB" none)) (.resize 8 (.lit (.ofNat 1 1))))) 0
-- …a ROOT conversion is an assignment-like target (a genvar initializer,
-- extractor `_sym_genvar_init`): where its reading (300) differs from the
-- own-width one (44) the root is loud, where they agree it is the value…
#guard isLoud (evalInt { nvals := [("U", (200, 8, false))] }
  (.resize 32 (.binary (.m0 .add) (.paramRef "U" none) (.resize 32 (lit8 100)))))
#guard okIs (evalInt { nvals := [("U", (20, 8, false))] }
  (.resize 32 (.binary (.m0 .add) (.paramRef "U" none) (.resize 32 (lit8 100))))) 120
-- …(`rf_gv`: `U + 1'b1` with a 4-bit `U = 15` is 0 in Icarus, 16 in slang
-- and Yosys; with `U = 3` both give 4), signed too (`S + S`, 4-bit `S = 7`:
-- -2 against 14)…
#guard isLoud (evalInt { nvals := [("U", (15, 4, false))] }
  (.resize 32 (.binary (.m0 .add) (.paramRef "U" none) (.resize 32 (.lit (.ofNat 1 1))))))
#guard okIs (evalInt { nvals := [("U", (3, 4, false))] }
  (.resize 32 (.binary (.m0 .add) (.paramRef "U" none) (.resize 32 (.lit (.ofNat 1 1)))))) 4
#guard isLoud (evalInt { nvals := [("S", (7, 4, true))] }
  (.signedResize 32 (.binary (.m0 .add) (.signedResize 32 (.paramRef "S" none))
    (.signedResize 32 (.paramRef "S" none)))))
#guard okIs (evalInt { nvals := [("S", (-3, 4, true))] }
  (.signedResize 32 (.binary (.m0 .add) (.signedResize 32 (.paramRef "S" none))
    (.signedResize 32 (.paramRef "S" none))))) (-6)
-- …and a value that a genvar's 32-bit `integer` would change is loud
-- (2^32 + 1 at 40 bits, 2^32 - 1 at 32 bits), one that survives is not.
#guard isLoud (evalInt { nvals := [("U", (4294967297, 40, false))] }
  (.resize 32 (.paramRef "U" none)))
#guard isLoud (evalInt { nvals := [("U", (4294967295, 32, false))] }
  (.resize 32 (.paramRef "U" none)))
#guard okIs (evalInt { nvals := [("U", (5, 40, false))] } (.resize 32 (.paramRef "U" none))) 5
-- An INT-class chain widened past 32 bits is NO target by itself — in a
-- value position the width is a sibling signal's (`a + P * 2`, `constAtCtx2`
-- re-evaluates at the operation width): read at its own 32 bits…
#guard okIs (evalInt { vals := [("N", 2147483647)] }
  (.binary (.m0 .add) (.signedResize 40 (.paramRef "N" none)) (.int 1))) (-2147483648)
-- …while an INT-class instance override into a 40-bit typed parameter
-- carries its root conversion (`_sym_override_root`): loud where the 32-bit
-- value overflows, the value where it does not.
#guard okIs (evalInt { vals := [("N", 5)] }
  (.signedResize 40 (.binary (.m0 .add) (.signedResize 40 (.paramRef "N" none)) (.int 1)))) 6
#guard isLoud (evalInt { vals := [("N", 2147483647)] }
  (.signedResize 40 (.binary (.m0 .add) (.signedResize 40 (.paramRef "N" none)) (.int 1))))
-- A self-determined root takes its own width HERE: with an 8-bit U (16
-- bits at the default point) the 16-bit `Resize`s of the literals are no
-- floor, `U + 8'd200 < 8'd50` compares at 8 bits — 100 + 200 wraps to 44.
#guard okIs (evalInt { nvals := [("U", (100, 8, false))] }
  (.binary (.m0 .lt) (.binary (.m0 .add) (.paramRef "U" none) (.resize 16 (lit8 200)))
    (.resize 16 (lit8 50)))) 1
-- An operand wider HERE than the default point's conversion is not
-- truncated: `U > 5` with a 40-bit U = 2^32 is true.
#guard okIs (evalInt { nvals := [("U", (4294967296, 40, false))] }
  (.binary (.m0 .gt) (.resize 32 (.paramRef "U" none)) (.int 5))) 1
-- A negative genvar zero-extended past 32 bits splits the oracles: loud.
#guard isLoud (evalInt (IEnv.bindNVal { vals := [("g", -1)] } "U" 0 40 false)
  (.binary (.m0 .add) (.resize 32 (.genvarRef "g")) (.paramRef "U" none)))
#guard okIs (evalInt { vals := [("g", -1)] }
  (.binary (.m0 .add) (.resize 32 (.genvarRef "g")) (.int 0))) 4294967295
-- Typed localparams bind through `evalAssign`: `logic [N-1:0] L1` at N = 16.
private def lpWide : PLocalParam :=
  { name := "L1", expr := l1,
    type? := some (.packed [⟨.int 15, .int 0⟩] none) }
#guard (match bindLocal {} lpWide with
  | .ok e => e.nvals.lookup "L1" == some (300, 16, false)
  | .error _ => false)
-- Round 4: an `integer`/`int` localparam or parameter default is a 32-bit
-- target (`evalIntTarget`; repros `rf_int`, `rf_ipar`): `U + 1'b1` with a
-- 4-bit `U = 15` is 16, not the 4-bit 0 — with or without the `Squash2` of
-- an `int` target.
private def uPlus1 : PExpr :=
  .binary (.m0 .add) (.paramRef "U" none) (.resize 32 (.lit (.ofNat 1 1)))
private def u15 : IEnv := { nvals := [("U", (15, 4, false))] }
private def int32Ty : PType := .packed [⟨.int 31, .int 0⟩] (some 32)
#guard (match bindLocal u15 { name := "L", expr := uPlus1, type? := some int32Ty } with
  | .ok e => e.vals.lookup "L" == some 16
  | .error _ => false)
#guard (match bindLocal u15 { name := "K", expr := .squash2 32 uPlus1, type? := some int32Ty } with
  | .ok e => e.vals.lookup "K" == some 16
  | .error _ => false)
#guard okIs (PParam.evalDefault u15 { name := "P", type? := some int32Ty } uPlus1) 16
-- An untyped localparam keeps its own type: `(U + 1'b1) >> 1` is 0 at 4 bits.
#guard (match bindLocal u15 { name := "X", expr := .binary .shr uPlus1 (.int 1) } with
  | .ok e => e.nvals.lookup "X" == some (0, 4, false)
  | .error _ => false)

/-! ### Round 5 folds: `Squash2`, declared signedness, untyped wraps

A `Squash2` is transparent to `ctype` (repro `vq_sq2`); a type with a
non-literal bound needs its envelope `signed` (repros `vq_sgn2`,
`vq_sgn3`); an untyped constant whose own-type value wraps is loud
(`evalUntyped`). -/

-- `localparam bit [N-1:0] B1 = (U + 1'b1) >> 1`: slang's `Squash2(32, …)`
-- (the default N = 32) is no floor at N = 4, U = 15 — 0 as in Icarus 12.0
-- and the Yosys 0.53 netlist (it was 8); an `int` target K still reads 8.
private def b1Expr : PExpr :=
  .squash2 32 (.binary .shr uPlus1 (.int 1))
private def bit4Ty : PType := .packed [⟨.int 3, .int 0⟩] none
private def lpB1 : PLocalParam :=
  { name := "B1", expr := b1Expr, type? := some bit4Ty, signed? := some false }
private def lpK : PLocalParam := { name := "K", expr := b1Expr, type? := some int32Ty }
private def pPB : PParam := { name := "PB", type? := some bit4Ty, signed? := some false }
#guard (match bindLocal u15 lpB1 with
  | .ok e => e.nvals.lookup "B1" == some (0, 4, false)
  | .error _ => false)
#guard (match bindLocal u15 lpK with
  | .ok e => e.vals.lookup "K" == some 8
  | .error _ => false)
#guard okIs (PParam.evalDefault u15 pPB b1Expr) 0
-- `logic signed [M-1:0] S`: without the envelope's `signed` the type is
-- loud; with it, the declared signedness at every width (S = -1 at M = 8
-- stays -1, where the default rule read it as 255).
private def tyM : PType := .packed [⟨.binary (.m0 .sub) (.paramRef "M" none) (.int 1), .int 0⟩] none
#guard (declConstType { vals := [("M", 8)] } (some tyM) none matches .error _)
#guard (declConstType { vals := [("M", 32)] } (some tyM) none matches .error _)
#guard (declConstType { vals := [("M", 8)] } (some tyM) (some true) matches .ok (some (8, true)))
#guard (declConstType { vals := [("M", 32)] } (some tyM) (some true) matches .ok none)
#guard (declConstType { vals := [("M", 32)] } (some tyM) (some false) matches .ok (some (32, false)))
#guard (declConstType {} (some int32Ty) none matches .ok none)
private def pMS : List PParam :=
  [{ name := "M", type? := some int32Ty }, { name := "S", type? := some tyM, signed? := some true }]
#guard (match bindParams {} pMS [8, -1] with
  | .ok e => e.nvals.lookup "S" == some (-1, 8, true)
  | .error _ => false)
-- `localparam Y = SB + 1'b1` (untyped, 8-bit SB): loud where it wraps (SB =
-- 255: 0 in slang and Yosys, 256 in Icarus) and, since round 6, where it
-- does not (SB = 5: 6 in every tool, but 9 bits wide in Icarus and 8 in
-- slang and Yosys — `Constant:untyped-width`); a RIGHT shift keeps its own
-- width and is admitted (`(U + 1'b1) >> 1` above is 0, as in Icarus). Round
-- 7: a LEFT shift widens in Icarus (`1 << N` is 32 + N bits), so `SB << 4`
-- is loud too, although Icarus keeps a sized left operand's 8 bits there (a
-- recorded over-refusal).
private def sbEnv (v : Int) : IEnv := { nvals := [("SB", (v, 8, false))] }
private def yExpr : PExpr :=
  .binary (.m0 .add) (.paramRef "SB" none) (.resize 8 (.lit (.ofNat 1 1)))
#guard (bindLocal (sbEnv 255) { name := "Y", expr := yExpr } matches .error _)
#guard (bindLocal (sbEnv 5) { name := "Y", expr := yExpr } matches .error _)
#guard isLoud (PParam.evalDefault (sbEnv 255) { name := "Q" } yExpr)
#guard isLoud (PParam.evalDefault (sbEnv 5) { name := "Q" } yExpr)
#guard isLoud (evalUntyped (sbEnv 255) (.binary .shl (.paramRef "SB" none) (.int 4)))
#guard isLoud (evalUntyped (sbEnv 255) (.binary .div yExpr (.lit (.ofNat 2 2))))
#guard isLoud (evalUntyped { vals := [("N", 2147483647)] }
  (.binary (.m0 .add) (.paramRef "N" none) (.int 1)))

/-! ### Round 6 folds: `Squash2` under a narrowing target, untyped widths

A `Squash2` under a `Resize` passes the context through (repro `vs_sqn`);
an untyped constant that Icarus 12.0 types wider than its own type is loud
(`PExpr.icarusWidens`, repros `vs_uw`, `vs_up`, `vs_uw3`, `vs_upw2`). -/

-- `localparam shortint H1 = (U + 1'b1) >> 1` and `localparam int KI = (UK +
-- 1'b1) >> 1`, with the default point's `Resize(16, Squash2(32, …))` and
-- `Resize(32, Squash2(40, …))`: at a 4-bit `U = 15` the 16- and 32-bit
-- targets are the context, 8 in Icarus 12.0, the Yosys 0.53 netlist and
-- slang (it was 0); `byte Y1 = U + 1'b1` is 16; at a 33-bit operand the
-- operand's own width is the context.
private def h1Expr (w d : Nat) : PExpr := .resize w (.squash2 d (.binary .shr uPlus1 (.int 1)))
private def shortTy : PType := .packed [⟨.int 15, .int 0⟩] (some 16)
private def byteTy : PType := .packed [⟨.int 7, .int 0⟩] (some 8)
private def lpH1 : PLocalParam :=
  { name := "H1", expr := h1Expr 16 32, type? := some shortTy, signed? := some true }
private def lpKI : PLocalParam := { name := "KI", expr := h1Expr 32 40, type? := some int32Ty }
private def lpY1 : PLocalParam :=
  { name := "Y1", expr := .resize 8 (.squash2 32 uPlus1), type? := some byteTy, signed? := some true }
private def pPY : PParam := { name := "PY", type? := some byteTy, signed? := some true }
#guard (match bindLocal u15 lpH1 with
  | .ok e => e.nvals.lookup "H1" == some (8, 16, true)
  | .error _ => false)
#guard (match bindLocal u15 lpKI with
  | .ok e => e.vals.lookup "KI" == some 8
  | .error _ => false)
#guard (match bindLocal u15 lpY1 with
  | .ok e => e.nvals.lookup "Y1" == some (16, 8, true)
  | .error _ => false)
#guard okIs (PParam.evalDefault u15 pPY (h1Expr 8 32)) 8
#guard (match bindLocal { nvals := [("U", (8589934591, 33, false))] } lpH1 with
  | .ok e => e.nvals.lookup "H1" == some (0, 16, true)
  | .error _ => false)
-- Untyped widths: `2 ** SB` (non-INT, a value beyond 64 extra bits at SB =
-- 100), `N + 1` (INT, 33 bits in Icarus) and `2 ** N` (INT, 42 bits in
-- Icarus at N = 40) are loud; `SB >> 1`, `SB == 8'd5` are not.
#guard isLoud (evalUntyped (sbEnv 100) (.binary .pow (.int 2) (.paramRef "SB" none)))
#guard isLoud (evalUntyped { vals := [("N", 5)] } (.binary (.m0 .add) (.paramRef "N" none) (.int 1)))
#guard isLoud (evalUntyped { vals := [("N", 8)] } (.binary .pow (.int 2) (.paramRef "N" none)))
#guard okIs (evalUntyped (sbEnv 6) (.binary .shr (.paramRef "SB" none) (.int 1))) 3
#guard okIs (evalUntyped (sbEnv 5) (.binary (.m0 .eq) (.paramRef "SB" none) (lit8 5))) 1

/-! ### Round 7 folds: left shifts widen, the `Squash2` own-width gate

An untyped constant with a LEFT shift is loud (`PExpr.icarusWidens`;
round 6 FOLDS verifier blocker 3, repros `vw_shl`, `vw_shp`, `vw_sho`): `1
<< N` is 32 + N bits in Icarus 12.0 (2^40 at `N = 40`, 0 in the Yosys 0.53
netlist). A 2-state target narrower than its initializer whose `Squash2`
operand is undefined at its OWN width stays loud (round 6 FOLDS verifier
major 4, repro `vw_sqd`): `localparam shortint H1 = 4'd8 / (U + 1'b1)` at
a 4-bit `U = 15` divides by zero at U's 4 bits (the round 5 reading) and
not at the 16-bit context (round 6's). -/

private def nEnv (n : Int) : IEnv := { vals := [("N", n)] }
private def oneShlN : PExpr := .binary .shl (.int 1) (.paramRef "N" none)
#guard isLoud (evalUntyped (nEnv 8) oneShlN)
#guard isLoud (evalUntyped (nEnv 40) oneShlN)
#guard isLoud (evalUntyped (nEnv 8) (.binary .ashl (.int 1) (.paramRef "N" none)))
#guard isLoud (evalUntyped (nEnv 8) (.binary (.m0 (.shl false)) (.int 1) (.paramRef "N" none)))
#guard isLoud (evalUntyped (nEnv 8) (.binary (.m0 .or) oneShlN (.int 1)))
#guard isLoud (evalUntyped (nEnv 8) (.binary .div oneShlN (.int 2)))
#guard isLoud (evalUntyped (nEnv 8) (.binary (.m0 .div) oneShlN (.int 2)))
#guard isLoud (evalUntyped (nEnv 8) (.binary (.m0 (.pow false false)) (.int 2) (.paramRef "N" none)))
#guard okIs (evalUntyped (nEnv 8) (.binary .shr (.int 256) (.paramRef "N" none))) 1
private def sqDiv : PExpr := .binary .div (.resize 32 (.lit (.ofNat 4 8))) uPlus1
private def lpSqD : PLocalParam :=
  { name := "H1", expr := .resize 16 (.squash2 32 sqDiv), type? := some shortTy, signed? := some true }
#guard (bindLocal u15 lpSqD matches .error _)
#guard (match bindLocal { nvals := [("U", (7, 4, false))] } lpSqD with
  | .ok e => e.nvals.lookup "H1" == some (1, 16, true)
  | .error _ => false)
#guard (bindLocal u15 { lpSqD with expr := .signedResize 16 (.squash2 32 sqDiv) } matches .error _)
-- The squash2-free twin is unchanged (0 at the 16-bit context, as before).
#guard (match bindLocal u15 { lpSqD with expr := .resize 16 sqDiv } with
  | .ok e => e.nvals.lookup "H1" == some (0, 16, true)
  | .error _ => false)

end LeanModels.Sv
