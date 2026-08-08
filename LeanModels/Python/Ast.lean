import LeanModels.Core.Basic

/-!
# Python AST (`LeanModels.Python`)

Lean inductives mirroring `docs/envelope-schema.md` (schema v0.1, Python payload).
Node and field vocabulary follows CPython's `ast` module; constructor names are
lowerCamelCase spellings of CPython's class names with a documented 1:1 mapping
(see each operator enum's docstring). Every statement/expression node carries its
source `LeanModels.Span`.

Unknown constructs are represented by `Expr.unsupported` / `Stmt.unsupported`
(carrying the CPython kind name and unparsed text), so ingestion never fails.

This file also defines the core value/result types from `docs/DESIGN.md`
("Core Lean types"): `Val`, `PyErr`, `Res`, `Flow`, `Env`. The interpreter
itself lives in a later phase (`Semantics.lean`).
-/

namespace LeanModels.Python

/-- Binary operators. 1:1 with CPython `ast` operator class names:
`add` ↔ `Add`, `sub` ↔ `Sub`, `mult` ↔ `Mult`, `floorDiv` ↔ `FloorDiv`,
`mod` ↔ `Mod`, `pow` ↔ `Pow`. -/
inductive BinOp where
  | add | sub | mult | floorDiv | mod | pow
deriving Repr, Inhabited, BEq, DecidableEq

/-- Unary operators. 1:1 with CPython: `usub` ↔ `USub`, `not` ↔ `Not`. -/
inductive UnaryOp where
  | usub | not
deriving Repr, Inhabited, BEq, DecidableEq

/-- Boolean (short-circuit) operators. 1:1 with CPython: `and` ↔ `And`, `or` ↔ `Or`. -/
inductive BoolOp where
  | and | or
deriving Repr, Inhabited, BEq, DecidableEq

/-- Comparison operators. 1:1 with CPython: `eq` ↔ `Eq`, `notEq` ↔ `NotEq`,
`lt` ↔ `Lt`, `ltE` ↔ `LtE`, `gt` ↔ `Gt`, `gtE` ↔ `GtE`, `is` ↔ `Is`,
`isNot` ↔ `IsNot`, `inOp` ↔ `In`, `notIn` ↔ `NotIn` (Lean-keyword-safe
spellings for the membership pair). Since H1-proper the extractor emits
`Is`/`IsNot` for EVERY identity comparison (H1 decides identity
dynamically: refs compare by address, `None` by the singleton test); the
interpreter loudly refuses the remaining out-of-tier operand forms
(identity between two non-`None` immediates — small-int caching, str
interning — is CPython-implementation-defined). -/
inductive CmpOp where
  | eq | notEq | lt | ltE | gt | gtE | is | isNot | inOp | notIn
deriving Repr, Inhabited, BEq, DecidableEq

/-- Literal constants (schema `Constant` payload). Ints are arbitrary precision
(JSON carries them as decimal strings). Float/bytes/complex/Ellipsis constants
never reach this type — the extractor emits them as `Unsupported` nodes. -/
inductive Const where
  | none
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
deriving Repr, Inhabited, BEq, DecidableEq

/-- A function parameter: schema `param` = `{"arg": …, "span": …}`, plus an
optional `"default"` const payload (F1). `default` is `some c` iff the
source gave this parameter a LITERAL default (int/bool/str/None) — the only
defaults in tier; a function with any non-literal default (a `Name`, a
negative number, `[]`, a call, …) instead keeps `argsOk = false` with no
per-param defaults, and calling it stays `unsupported`. -/
structure Param where
  arg : String
  span : Span
  default : Option Const := Option.none
deriving Repr, Inhabited, BEq, DecidableEq

/-- Expressions. Constructor ↔ schema `kind` mapping:
`constant` ↔ `Constant`, `name` ↔ `Name`, `binOp` ↔ `BinOp`,
`unaryOp` ↔ `UnaryOp`, `boolOp` ↔ `BoolOp`, `compare` ↔ `Compare`,
`call` ↔ `Call`, `list` ↔ `List`, `tuple` ↔ `Tuple`,
`subscript` ↔ `Subscript`, `slice` ↔ `Slice`, `unsupported` ↔ `Unsupported`. -/
inductive Expr where
  | constant (value : Const) (span : Span)
  | name (id : String) (span : Span)
  | binOp (left : Expr) (op : BinOp) (right : Expr) (span : Span)
  | unaryOp (op : UnaryOp) (operand : Expr) (span : Span)
  | boolOp (op : BoolOp) (values : Array Expr) (span : Span)
  | compare (left : Expr) (ops : Array CmpOp) (comparators : Array Expr) (span : Span)
  | call (func : Expr) (args : Array Expr) (callUnsupported : Option String) (span : Span)
  | list (elts : Array Expr) (span : Span)
  | tuple (elts : Array Expr) (span : Span)
  | subscript (value : Expr) (index : Expr) (span : Span)
  | dict (keys : Array Expr) (values : Array Expr) (span : Span)
  | attribute (value : Expr) (attr : String) (span : Span)
  /-- Conditional expression `body if test else orelse` (schema `IfExp`,
  H5): lazy — exactly one branch evaluates, CPython order. -/
  | ifExp (test : Expr) (body : Expr) (orelse : Expr) (span : Span)
  /-- Slice subscript `value[lower:upper:step]` (schema `Slice`, H5
  strings — sunfish's `board[::-1]` / `board[:i]`). Components the source
  omits are filled by INGESTION with `Constant None` — CPython's own
  compilation (`BUILD_SLICE` pushes `None` for a missing bound), so
  `s[:i]` and `s[None:i:None]` are the SAME node, faithfully. -/
  | slice (value : Expr) (lower : Expr) (upper : Expr) (step : Expr) (span : Span)
  | unsupported (pyKind : String) (text : String) (span : Span)
deriving Repr, Inhabited, BEq
-- DecidableEq deriving does not cope with the nested `Array Expr`; derived BEq suffices.

/-- Statements. Constructor ↔ schema `kind` mapping (Lean-keyword-safe names):
`ret` ↔ `Return`, `assign` ↔ `Assign`, `augAssign` ↔ `AugAssign`,
`whileLoop` ↔ `While`, `forStmt` ↔ `For`, `ifStmt` ↔ `If`, `exprStmt` ↔ `Expr`,
`pass` ↔ `Pass`, `brk` ↔ `Break`, `cont` ↔ `Continue`,
`unsupported` ↔ `Unsupported`.

`FunctionDef` has no `Stmt` constructor: at module top level it becomes a
`FunctionDefn` in `Module.functions`; a *nested* `def` is ingested as
`Stmt.unsupported "FunctionDef" name span` (v0 has no closures anyway). -/
inductive Stmt where
  | ret (value : Option Expr) (span : Span)
  | assign (targets : Array Expr) (value : Expr) (span : Span)
  | augAssign (target : Expr) (op : BinOp) (value : Expr) (span : Span)
  | whileLoop (test : Expr) (body : Array Stmt) (orelse : Array Stmt) (span : Span)
  | forStmt (target : Expr) (iter : Expr) (body : Array Stmt) (orelse : Array Stmt) (span : Span)
  | ifStmt (test : Expr) (body : Array Stmt) (orelse : Array Stmt) (span : Span)
  | exprStmt (value : Expr) (span : Span)
  | pass (span : Span)
  | brk (span : Span)
  | cont (span : Span)
  | unsupported (pyKind : String) (text : String) (span : Span)
deriving Repr, Inhabited, BEq
-- DecidableEq deriving does not cope with the nested `Array Stmt`; derived BEq suffices.

/-- A module-level function definition (schema `FunctionDef`).
`argsOk` is DESIGN.md's `paramsOk`: `false` iff the schema's `args_unsupported`
was non-null (NON-literal defaults / `*args` / kw-only / `**kwargs` /
decorators), in which case calling the function is `unsupported`. Plain
positional params are always listed in `params`; literal defaults ride on
the params themselves (`Param.default`) and do NOT set `argsOk = false`. -/
structure FunctionDefn where
  name : String
  params : Array Param
  argsOk : Bool
  /-- `false` when the body calls a name that is also assigned somewhere in the
  same body: CPython's static-locals rule makes such a name local *throughout*
  the body (calls before the assignment raise `UnboundLocalError`), which the
  dynamic-env interpreter cannot reproduce — calling such a function is
  `unsupported` (loud) rather than silently resolving to the module table.
  Mirrors `argsOk`; set from the envelope's `locals_unsupported`. -/
  localsOk : Bool := true
  /-- Does the function's subtree (nested scopes included) contain a
  `global` statement? Set from the envelope's `has_global` (absent =
  `false`). Consumed by the ingestion namedtuple census: a `global` can
  rebind a module name when the function is called, which would make the
  recognized table silently stale — the census refuses such modules. -/
  hasGlobal : Bool := false
  body : Array Stmt
  span : Span
deriving Repr, Inhabited, BEq
-- No DecidableEq: `Stmt` has none (nested arrays).

/-- A module-level namedtuple class (H3+, docs/memory-model.md §class
semantics — the recorded VALUE-like decision): recognized at INGESTION
from a top-level `X = namedtuple("T", <fields>)` assignment under the
exact benign import `from collections import namedtuple`, subject to the
conservative binding census (see `Json.lean`); unrecognized shapes stay
ordinary assignments (poisoned G1 bindings — loud, never wrong).
`name` is the BOUND module-level name (constructor resolution); `tname`
the typename argument (CPython error messages name it; the harness
compares exception classes only); `fields` the validated field names in
declaration order. Instances are immediate `RVal.ntuple` VALUES — no
heap identity, tuple equality/hashing — so a `NamedTupleId` table index
is unnecessary: the value carries its own `tname`/`fields`. -/
structure NamedTupleDefn where
  name : String
  tname : String
  fields : Array String
  span : Span
deriving Repr, Inhabited, BEq, DecidableEq

/-- A module-level class definition (schema `ClassDef`, H3). The class's
METHOD BODIES are not stored here: ingestion FLATTENS them into
`Module.functions` under qualified names `"<class>.<method>"` (a Python
identifier can never contain `.`, so qualified names collide with nothing
and plain-name resolution never sees them) — method calls then reuse
`callIn`/`CallsIn` verbatim, with `self` as an ordinary first argument.
`methods` records the plain method names (dispatch/guard checks);
`ok = false` iff the class uses features outside the tier (bases —
inheritance is loudly unsupported — keywords/metaclass, decorators,
class-level statements other than defs/docstrings/`pass`): the class is
still REPRESENTED, but instantiating it refuses loudly.

Class identity (docs/memory-model.md H3): a `ClassId` is the INDEX into
`Module.classes`, never the name. With duplicate class names the LAST
definition wins everywhere consistently: instantiation resolves the name
to the last index (`findClassIdx`, findRev), and the flattened qualified
method names also resolve last-wins (`findFunction`, findRev) — an
instance of an earlier same-named class is unconstructible. -/
structure ClassDefn where
  name : String
  ok : Bool
  methods : Array String
  /-- `has_global` of the whole class subtree (class-level statements
  included — `class C: global x; x = 1` rebinds a module name at import
  time). See `FunctionDefn.hasGlobal`. -/
  hasGlobal : Bool := false
  /-- The recognized namedtuple BASE of a value-like subclass
  (`class Position(namedtuple("Position", "…"))` — sunfish's shape):
  instantiation then builds an IMMEDIATE `RVal.ntuple` value, exactly
  like a plain recognized namedtuple (methods on the immutable self are
  the recorded next tier). Set by ingestion ONLY when the extractor's
  structured `namedtuple_base` validates AND the module-level namedtuple
  census passes (benign import, `namedtuple` unshadowed — Json.lean);
  otherwise the class demotes to the ordinary uninstantiable-loudly
  state (`ok = false`). The inner `NamedTupleDefn.name` is the CLASS
  name (the constructor callers resolve). -/
  ntBase : Option NamedTupleDefn := Option.none
  span : Span
deriving Repr, Inhabited, BEq, DecidableEq

/-- A Python module: `def`s split out into `functions` (in source order,
including class methods flattened under `"<class>.<method>"` qualified
names — see `ClassDefn`); `class`es split into `classes` (in source
order); recognized namedtuple classes split into `namedtuples` (in source
order — see `NamedTupleDefn`); all other top-level statements recorded in
`topLevel` (in source order). -/
structure Module where
  functions : Array FunctionDefn
  topLevel : Array Stmt
  classes : Array ClassDefn := #[]
  namedtuples : Array NamedTupleDefn := #[]
deriving Repr, Inhabited, BEq
-- No DecidableEq: `Stmt`/`FunctionDefn` have none (nested arrays).

/-! ## Core value / result types (DESIGN.md, normative) -/

/-- Runtime values. -/
inductive Val where
  | none
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  | list (xs : Array Val)
  | tuple (xs : Array Val)
deriving Repr, Inhabited, BEq
-- DecidableEq deriving does not cope with the nested `Array Val`; derived BEq
-- suffices (`#guard` checks use `==` on `Res Val`, per DESIGN.md).

/-- Python runtime errors representable in the tier. Canonical harness names:
`TypeError`, `NameError`, `ZeroDivisionError`, `IndexError`, `ValueError`,
since H1-proper (the dict tier) `KeyError` (missing dict key),
`RuntimeError` (dict changed size during iteration), `RecursionError`
(cyclic dict comparison), and since H3 (classes) `AttributeError` (missing
instance attribute; attribute access on builtins outside their method
tier). The harness compares exception *class names* only, so message-free
constructors (`keyError`/`attributeError` like `indexError`) carry no
payload. -/
inductive PyErr where
  | typeError (msg : String)
  | nameError (name : String)
  | zeroDivisionError
  | indexError
  | valueError (msg : String)
  | keyError
  | runtimeError (msg : String)
  | recursionError
  | attributeError
deriving Repr, Inhabited, BEq, DecidableEq

/-- Interpreter results. `unsupported` = outside the v0 tier (loud), NOT a Python error. -/
inductive Res (α : Type) where
  | ok (a : α)
  | exn (e : PyErr)
  | timeout
  | unsupported (msg : String)
deriving Repr, Inhabited, BEq, DecidableEq

instance : Monad Res where
  pure := .ok
  bind r f :=
    match r with
    | .ok a => f a
    | .exn e => .exn e
    | .timeout => .timeout
    | .unsupported msg => .unsupported msg

/-- Statement-level control flow. -/
inductive Flow where
  | next
  | ret (v : Val)
  | brk
  | cont
deriving Repr, Inhabited, BEq
-- No DecidableEq: `Val` has none (nested arrays).

-- `Env` (local environments) lives in `Runtime.lean` since the H1 core
-- re-shape: environments bind names to *runtime* values (`RVal`), while
-- `Val` here remains the frozen public boundary type.

end LeanModels.Python
