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
`mod` ↔ `Mod`, `pow` ↔ `Pow`, `lshift` ↔ `LShift`, `bitOr` ↔ `BitOr`
(pass 5 — docs/memory-model.md §left shift and bitwise or), `bitAnd` ↔
`BitAnd` (the tail batch — docs/memory-model.md §bitwise `&`). -/
inductive BinOp where
  | add | sub | mult | floorDiv | mod | pow | lshift | rshift
  | bitOr | bitXor | bitAnd
deriving Repr, Inhabited, BEq, DecidableEq

/-- Unary operators. 1:1 with CPython: `usub` ↔ `USub`, `not` ↔ `Not`,
`uadd` ↔ `UAdd`, `invert` ↔ `Invert`. -/
inductive UnaryOp where
  | usub | not | uadd | invert
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
  /-- Call. `kwargs` are the structured plain named keywords (H6,
  docs/memory-model.md §call-site keyword arguments), evaluated AFTER
  the positionals, left to right — source order, since Python forbids a
  positional after a keyword. `**` unpacking and starred args ride in
  `callUnsupported` (loud). -/
  | call (func : Expr) (args : Array Expr) (kwargs : Array (String × Expr))
      (callUnsupported : Option String) (span : Span)
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
  /-- Generator EXPRESSION `(elt for target in iter if ifs…)` (schema
  `GeneratorExp`, H4 — the single-clause, non-`async` shape; anything
  else stays `Unsupported`). The node is STRUCTURED here but never
  survives ingestion: `parseModule` LOWERS every occurrence to a call of
  a freshly synthesized generator function taking the already-evaluated
  outer iterable as its first argument — exactly how CPython compiles a
  genexp (`MAKE_FUNCTION <genexpr>; GET_ITER; CALL_FUNCTION 1`). The
  constructor exists so the lowering is a total function on a typed AST
  rather than a JSON rewrite, and so a genexp that ingestion REFUSES to
  lower (a free variable the enclosing body rebinds — capture by value
  would differ from CPython's capture by reference) is still
  representable and refuses loudly at evaluation. -/
  | genExp (elt : Expr) (target : Expr) (iter : Expr) (ifs : Array Expr)
      (walrus : Array (String × Expr)) (span : Span)
  /-- The WALRUS `(x := e)` in general expression position (schema
  `NamedExpr`, H7+ — docs/memory-model.md §the walrus operator).
  Evaluates `e`, BINDS `x` in the executing frame, and answers the same
  value. Only a plain NAME target is Python-legal, so the target is a
  `String`. The genexp-FILTER walrus keeps its own lowering
  (`genExp`'s `walrus` field, pass 7): a comprehension is its own scope
  and PEP 572 leaks the binding to the ENCLOSING one, which the lowering
  models and this constructor must not silently re-scope. -/
  | namedExpr (target : String) (value : Expr) (span : Span)
  | unsupported (pyKind : String) (text : String) (span : Span)
deriving Repr, Inhabited, BEq
-- DecidableEq deriving does not cope with the nested `Array Expr`; derived BEq suffices.

/-- Statements. Constructor ↔ schema `kind` mapping (Lean-keyword-safe names):
`ret` ↔ `Return`, `assign` ↔ `Assign`, `augAssign` ↔ `AugAssign`,
`whileLoop` ↔ `While`, `forStmt` ↔ `For`, `ifStmt` ↔ `If`, `exprStmt` ↔ `Expr`,
`pass` ↔ `Pass`, `brk` ↔ `Break`, `cont` ↔ `Continue`,
`importFrom` ↔ `ImportFrom` (structured, Pass 0), `unsupported` ↔ `Unsupported`.

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
  /-- `yield e` in STATEMENT position (schema `Yield`, H4 generators) —
  the ONLY yield the tier admits. A yield in EXPRESSION position is a
  `send` receiver (`x = yield v`) and stays `Expr.unsupported`, so no
  statement here can silently drop a sent value. A bare `yield` ingests
  as `yield None`, CPython's own compilation. -/
  | yieldStmt (value : Expr) (span : Span)
  /-- `yield from e` in STATEMENT position (schema `YieldFrom`, pass 5 —
  docs/memory-model.md §yield from). The admitted `<genexp>` iterable is
  INLINED at ingestion into `for target in iter: yield elt` (CPython-
  exact in tier: during a delegation the enclosing frame provably cannot
  run, so the inlined loop reads the same frame at the same points —
  by-reference, no capture analysis), so this constructor survives
  ingestion only UN-lowered — a non-genexp iterable, a target used
  elsewhere in the body, an unanalyzable target — and both executors
  (`execStmt`, `genPlan`) refuse it loudly with the reason. -/
  | yieldFromStmt (value : Expr) (span : Span)
  /-- A nested `def` DIRECTLY inside a function body (schema `NestedDef`,
  H7 — docs/memory-model.md §nested defs and closures), carried INLINE:
  no `Module.functions` flattening, no qname scheme. Executing it
  SNAPSHOTS `captures` from the current frame and allocates
  `Obj.closure`; the snapshot tier's admission (never-rebound-after-def,
  no `nonlocal`, one level deep, direct child of the body) is decided at
  EXTRACTION — anything outside it ships as `Stmt.unsupported` with the
  precise reason. `argsOk`/`localsOk`/`hasGlobal`/`isGenerator` are the
  nested body's own censuses, exactly `FunctionDefn`'s. -/
  | defStmt (name : String) (params : Array Param) (argsOk localsOk : Bool)
      (hasGlobal : Bool) (isGenerator : Bool) (body : Array Stmt)
      (captures : Array String) (span : Span)
  /-- `raise` (schema `Raise`, the exceptions tier — docs/memory-model.md
  §exceptions). Structured in FULL generality (`exc`/`cause` both
  optional, any expressions); EVALUATION admits exactly `raise N` where
  `N` names an admitted exception class (`class N(Exception): pass`,
  `ClassDefn.isExc`) — bare `raise`, `raise <expr>`, `raise N(args…)`
  and `raise … from …` all refuse loudly there, never here. -/
  | raiseStmt (exc : Option Expr) (cause : Option Expr) (span : Span)
  /-- `assert test` / `assert test, msg` (schema `Assert`, the tail batch
  — docs/memory-model.md §the assert statement). CPython compiles this to
  `if not test: raise AssertionError(msg)` guarded by `__debug__`; the
  model runs the way CPython runs by DEFAULT (no `-O`), so the test is
  always evaluated and the statement is never compiled away. `msg` is
  evaluated ONLY on the failing path — CPython's laziness, which is
  observable whenever the message expression has an effect. -/
  | assertStmt (test : Expr) (msg : Option Expr) (span : Span)
  /-- `try`/`except` (schema `Try`, the exceptions tier): the v0 shape —
  ONE handler naming ONE class, no `as` binding, no `else`, no
  `finally` — carried structurally (`excName` the handler's class name,
  `handler` its body). Everything outside the shape rides the
  `callUnsupported` pattern: the extractor fills `tryUnsupported` with
  the reason and EXECUTION refuses with it (structured-but-loud; the
  body/handler carried best-effort so censuses stay exact). Matching is
  class IDENTITY on the admitted exception kind, PLUS (Pass 0, §import
  forms) the pinned two-name import-error table
  (`importErrorHandlerMatch`) when `findClass` misses; a handler naming
  anything else (other builtin exception names, `Exception` itself)
  refuses loudly at execution, before the body runs (statically-first —
  the recorded as-built delta). -/
  | tryStmt (body : Array Stmt) (excName : String) (handler : Array Stmt)
      (tryUnsupported : Option String) (span : Span)
  /-- `del name, …` (schema `Delete`, the tail batch — docs/memory-model.md
  §the del statement). BARE NAMES only: `del d[k]`, `del o.attr`,
  `del xs[i]` are measured second tables and ship as `Stmt.unsupported`
  (extractor clause 4). No target is ever a subexpression, so the
  constructor carries plain strings and every expression walker is
  indifferent to it. The effect is PARTIAL, left to right (CPython:
  `del x, nosuch` really removes `x` before raising on `nosuch`), so
  both runtime arms thread state per target. Function scope: the census
  (extractor clauses 1–2) guarantees no admitted body reads a deleted
  name, so the arm's miss case is only ever `del` of a never-bound name —
  refused loudly, never a fabricated `UnboundLocalError`. Module scope
  (script surface only): locals ARE the globals under the one pipeline,
  so a hit removes and publishes, and a miss is CPython's faithful
  `NameError` — except dunder, benign-import and definition names, which
  refuse loudly (docs/backlog.md §del RECONCILED); a TRAILING `del` of
  definition names is rewritten away at ingestion. -/
  | delStmt (names : Array String) (span : Span)
  /-- `from module import names` / `from module import *` (schema
  `ImportFrom`, Pass 0 — docs/memory-model.md §import forms (Pass 0)).
  Structured by the EXTRACTOR for exactly the admitted shape (top-level,
  absolute, undotted, no aliases, names-or-star, and absent-module or
  guarded position — the extractor owns that admission against the
  pinned platform inventory; the Lean side carries no inventory).
  Pass 0 semantics: the importable universe is EMPTY — executing this
  RAISES `.importError module` unconditionally, never `.ok`; the
  guarded fallback path then runs through the ordinary exceptions
  machinery via the pinned two-name handler table
  (`importErrorHandlerMatch`). `star = true` is `import *` (`names`
  empty; its bind set is unknowable without a module, so every binding
  census answers `none` for it — unanalysable by fiat). The FUTURE
  modeled-module arm binds through this same constructor (recorded so
  Pass 0 does not foreclose it); today it binds nothing. Ingestion
  canonicalizes the benign-whitelist collision back to the legacy
  `.unsupported "ImportFrom" text` node (Json.lean, one rewrite site). -/
  | importFrom (module : String) (names : Array String) (star : Bool) (span : Span)
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
  /-- Is this a GENERATOR function (H4)? Set from the envelope's
  `is_generator` (absent = `false`), which the extractor computes by
  CPython's rule: the def's OWN scope contains a `yield`/`yield from`,
  reachable or not. Calling such a function never runs its body — it
  ALLOCATES a suspended frame (`Obj.generator`) and returns it — so this
  flag changes what a CALL means, exactly like `argsOk`/`localsOk`
  change whether one is allowed at all.

  Field position note (recorded finding, `py_vcgen`): `VCTactic.lean`
  reads `FunctionDefn.mk`'s BODY positionally — keep it in sync when
  these fields change. -/
  isGenerator : Bool := false
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
  /-- The THIRD recognized class kind (docs/memory-model.md §exceptions):
  an EXCEPTION class, the exact shape `class N(Exception): pass`.
  Recognized at ingestion (extractor marker `exception_base` + the
  module census proving `Exception` unshadowed — Json.lean); demoted to
  the ordinary loud state (`isExc := false`, `ok := false`) by any
  deviation. Such a class is an exception NAME, not an instantiable
  object: `raise N` maps to `.exn (.user cid name)`; calling `N(…)`
  refuses loudly (the value-position refusals are what keep the
  payload-free representation exact). -/
  isExc : Bool := false
  /-- Is CREATING this class observationally free? CPython executes a
  class body — and evaluates its bases — at the `class` statement, while
  the model builds `ClassDefn` at ingestion and executes nothing. That is
  invisible only when the body can neither print, raise, nor call: methods,
  `pass`, docstrings and LITERAL attribute assignments qualify; a call, a
  name read, an unrecognized base or a decorator does not (leanpy found the
  hole with `class C: print(…)` — CPython printed, the model did not, a
  WRONG ANSWER rather than a refusal). Set by ingestion from the class
  body (Json.lean); `runScript` refuses a module that contains a
  non-`creationPure` class, so a script never silently skips an effect.
  Default `false`: a hand-built `ClassDefn` has no body to inspect, and
  the safe answer is the loud one. -/
  creationPure : Bool := false
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

/-- The EXACT import statements the tier treats as BENIGN, with the name
each of them binds and whether the interpreter MODELS that name.

An import is not benign in general: executing one runs the imported
module's top level, and a circular import can rebind or mutate names in
*this* module before it finishes. So this is a whitelist of exact
statement TEXTS, never a shape rule — `import time` is admitted, `import
sitecustomize` is not, and anything not listed keeps the blunt behaviour
(the whole module's binding set becomes unknown).

`true` in the second component means the model already gives the bound
name a meaning (`count` IS `itertools.count` in `isBuiltinName`), so G1
binds nothing and resolution falls through to it; `false` means the value
is outside the tier, and G1 binds the name POISONED, so a read refuses
loudly instead of faking a `NameError` for a name CPython did bind.

The namedtuple ingestion census (`isBenignNtImport`, Json.lean)
established this whitelist for its single member and reads it from here —
one table, so a new row is reviewed once. -/
def benignImportBinds : String → Option (String × Bool)
  | "import time" => some ("time", false)
  | "from itertools import count" => some ("count", true)
  | "from collections import namedtuple" => some ("namedtuple", false)
  | _ => Option.none

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
tier), and since H4 (generators) `StopIteration`. The harness compares exception *class names* only, so message-free
constructors (`keyError`/`attributeError` like `indexError`) carry no
payload. -/
inductive PyErr where
  | typeError (msg : String)
  | nameError (name : String)
  /-- `x // 0` and `x % 0` — CPython's
  `integer division or modulo by zero`. -/
  | zeroDivisionError
  /-- `0 ** <negative>` — the SAME CPython class with a DIFFERENT text,
  `0.0 cannot be raised to a negative power` (2026-08-15).

  A sibling NULLARY constructor rather than a `String` payload on
  `zeroDivisionError`, and the reason is the whole design: the message is
  not runtime data, it is determined by WHICH of two raise conditions
  fired, and both are statically distinguishable in `evalBinOp`. Splitting
  keeps every existing `.zeroDivisionError` site — 40 of them, including
  `arith`'s four public theorem statements and their proofs — spelled
  exactly as it is today, so a message gap closes at ZERO cost to the
  spec surface. A payload would have changed all of them.

  `except ZeroDivisionError:` needs no update: builtin exception names are
  not matchable at all (only admitted user classes and the pinned
  import-error names), so the two cannot be told apart by any program in
  the tier. -/
  | zeroDivisionPow
  | indexError
  | valueError (msg : String)
  | keyError
  | runtimeError (msg : String)
  | recursionError
  | attributeError
  /-- A failed `assert` (the tail batch — docs/memory-model.md §the
  assert statement). The payload is `str()` of the message expression,
  rendered by `printOne` — `print`'s own one-argument rendering, shared
  rather than duplicated because it is the SAME CPython operation.
  `none` is the bare `assert test`, for which CPython prints the class
  alone: unlike `IndexError`/`KeyError` this constructor is EXACT, so
  `errMessage` answers it rather than reporting a gap. -/
  | assertionError (msg : Option String)
  /-- H4: `next(g)` on an exhausted generator. CPython's `StopIteration`
  is an ordinary exception (it is what ends a `for` loop internally); the
  tier raises it only from an explicit `next` without a default — the
  `for`-loop and `next(g, d)` paths CONSUME exhaustion instead. -/
  | stopIteration
  /-- Pass 0 (docs/memory-model.md §import forms (Pass 0)): a
  from-import of a module the model does not provide — in Pass 0 the
  importable universe is empty, so every executed `Stmt.importFrom`
  raises this. CPython 3.9 raises the SUBCLASS `ModuleNotFoundError`
  with message `No module named '{modName}'`; the boundary renders both
  exactly (`errName`/`errMessage`, Main.lean), so the uncaught case is
  `status exn`, exit 1, class line identical to the oracle. Handler
  matching is the PINNED two-name table (`importErrorHandlerMatch`,
  Semantics.lean): handler names `ImportError` and `ModuleNotFoundError`
  both match this kind — never a hierarchy walk. -/
  | importError (modName : String)
  /-- A USER exception (the exceptions tier, docs/memory-model.md
  §exceptions): class-identity, no payload — `raise N` of an admitted
  `class N(Exception): pass` IS its class. `cid` is the `ClassId` (the
  `Module.classes` index — identity for handler matching and `==`);
  `name` is the class name, carried so the boundary can render
  CPython's `type(e).__name__` without the module in hand (within one
  module the cid determines it, so equality on both is equality on the
  cid). The instance CPython implicitly builds can never be inspected
  (args/attrs/`as`-bindings all refuse loudly), which is what makes the
  class-identity representation observationally exact. -/
  | user (cid : Nat) (name : String)
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

/-! ### Builtin name tables

Defined here (not `Semantics.lean`, their original home — moved verbatim
2026-08-14, docs/memory-model.md §module-level def aliasing) because the
INGESTION census (`Json.lean`) consults them too, and `Json.lean` /
`Semantics.lean` are siblings above `Ast`/`Runtime`. -/

/-- Builtin names the interpreter implements (resolution: shadowable by
locals, module globals, and module `def`s, exactly like CPython builtins). -/
def isBuiltinName (id : String) : Bool :=
  id == "len" || id == "sorted" || id == "max" || id == "min" ||
  id == "abs" || id == "int" || id == "print" ||
  id == "str" || id == "input" ||
  id == "ord" || id == "chr" || id == "next" ||
  -- §iter: `iter` was in `isPyBuiltinName` and NOT here — the two-table gap
  -- §pycomplete-14 was caught by. It joins DELIBERATELY: a name in this list
  -- is one every `NameError` decision treats as bound, and one a bare-name
  -- read refuses as "referencing builtin '…' as a value" rather than as an
  -- unmodelled builtin. Both were refusals before and both still are; the
  -- MESSAGE moves, and it moves to the truer one.
  id == "enumerate" || id == "count" || id == "iter" ||
  id == "any" || id == "all" || id == "set" ||
  id == "sum" || id == "tuple" || id == "range" || id == "list" ||
  id == "dict"

/-- Every name CPython 3.9's `builtins` module binds (`dir(builtins)`,
minus the dunders — generated from the PINNED reference interpreter).

`isBuiltinName` above is the subset the model IMPLEMENTS. This is the
subset CPython BINDS, and the difference is exactly the set of names for
which a `NameError` would be a WRONG ANSWER: the name resolves in
CPython, so the honest outcome is a loud refusal.

FOUND BY `tools/leanpy` (2026-08-13) on the shipped sunfish.py:
`opt_ranges = dict(QS=(0, 300), …)` answered `NameError` where CPython
builds a dict — and the same hole was reachable from an ordinary function
body (`def f(): return len(dict()))`, so it was never a script-mode
artifact. Every name-resolution arm that may DECIDE a `NameError` now
consults this list first. -/
def isPyBuiltinName (id : String) : Bool :=
  [
   "ArithmeticError", "AssertionError", "AttributeError", "BaseException",
   "BlockingIOError", "BrokenPipeError", "BufferError", "BytesWarning",
   "ChildProcessError", "ConnectionAbortedError", "ConnectionError",
   "ConnectionRefusedError", "ConnectionResetError", "DeprecationWarning",
   "EOFError", "Ellipsis", "EnvironmentError", "Exception", "False",
   "FileExistsError", "FileNotFoundError", "FloatingPointError",
   "FutureWarning", "GeneratorExit", "IOError", "ImportError",
   "ImportWarning", "IndentationError", "IndexError", "InterruptedError",
   "IsADirectoryError", "KeyError", "KeyboardInterrupt", "LookupError",
   "MemoryError", "ModuleNotFoundError", "NameError", "None",
   "NotADirectoryError", "NotImplemented", "NotImplementedError", "OSError",
   "OverflowError", "PendingDeprecationWarning", "PermissionError",
   "ProcessLookupError", "RecursionError", "ReferenceError",
   "ResourceWarning", "RuntimeError", "RuntimeWarning", "StopAsyncIteration",
   "StopIteration", "SyntaxError", "SyntaxWarning", "SystemError",
   "SystemExit", "TabError", "TimeoutError", "True", "TypeError",
   "UnboundLocalError", "UnicodeDecodeError", "UnicodeEncodeError",
   "UnicodeError", "UnicodeTranslateError", "UnicodeWarning", "UserWarning",
   "ValueError", "Warning", "ZeroDivisionError", "abs", "all", "any",
   "ascii", "bin", "bool", "breakpoint", "bytearray", "bytes", "callable",
   "chr", "classmethod", "compile", "complex", "copyright", "credits",
   "delattr", "dict", "dir", "divmod", "enumerate", "eval", "exec", "exit",
   "filter", "float", "format", "frozenset", "getattr", "globals", "hasattr",
   "hash", "help", "hex", "id", "input", "int", "isinstance", "issubclass",
   "iter", "len", "license", "list", "locals", "map", "max", "memoryview",
   "min", "next", "object", "oct", "open", "ord", "pow", "print", "property",
   "quit", "range", "repr", "reversed", "round", "set", "setattr", "slice",
   "sorted", "staticmethod", "str", "sum", "super", "tuple", "type", "vars",
   "zip"
  ].contains id

end LeanModels.Python

/-! ## §3c-i-b — the dict-view INGESTION rewrite's vocabulary

A dict view in CONSUMING-ARGUMENT position is rewritten at ingestion to a
synthetic builtin over the receiver: `list(d.keys())` ⇢ `list(<dictkeys>(d))`.

**This is the THIRD place a construct's meaning is decided** — after the
extractor and the interpreter — and it is the same mechanism `ListComp` and
`yield from <genexp>` already use (docs/memory-model.md §list comprehensions,
§yield from). A capability audit that reads only the extractor and the
evaluator will not see it, which is why it is named here and in
docs/backlog/python-completeness.md.

Why ingestion and not the evaluator: fusion needs the RECEIVER, and the
fuel-free evaluator is structural on `Expr`, so a receiver produced by a pure
recognizer is not a subterm the equation compiler can see (2026-08-23-
pycomplete-10). Rewriting the ARGUMENT sidesteps it — the receiver then rides
the ordinary argument path. -/

/-- The synthetic builtin a dict view lowers to. The angle brackets make the
name unspellable in Python, the `<genexpr@n>` convention, so it can never
collide with a user binding — and it is deliberately NOT added to
`isBuiltinName`, which is the pinned CPython `dir(builtins)` and load-bearing
for every `NameError` decision. -/
def dictViewBuiltinName : String → Option String
  | "keys" => some "<dictkeys>"
  | "values" => some "<dictvalues>"
  | "items" => some "<dictitems>"
  | _ => Option.none

/-- §3c-i-c/§del: `del d[k]` lowers to `<dictdel>(d, k)` — an `exprStmt` over
a synthetic call, so the statement needs NO `Stmt` constructor and no walker
arm. Measured before choosing: a `delSubscript` constructor would have cost
~25 mechanical sites (`delStmt` has 28 occurrences across 9 files,
`assertStmt` 22 across 8) against this shape's six, and none of those 25
decide anything. `del` is a statement with no value and `exprStmt` DISCARDS
the value, so the lowering is exact rather than approximate.

Like the view names this is unspellable, checked before `isBuiltinName` and
kept OUT of it, and — the property that licenses it — it can never appear in
EXPRESSION position, because ingestion emits it only from a `Delete` node. -/
def dictDelBuiltinName : String := "<dictdel>"

/-- §PEP 289: the synthesized genexp function's name PREFIX, and its implicit
first parameter. Ingestion mints the names (`Json.lean`) and the EVALUATOR has
to recognise them, because PEP 289 gives a genexp a creation-time rule that an
ordinary generator function does not have — so the vocabulary lives here, with
the other names both sides read, rather than being spelled twice. -/
def genExpPrefix : String := "<genexpr@"

/-- CPython's own name for a genexp's implicit first parameter (the
already-evaluated outer iterable). No Python identifier contains `.`. -/
def genExpArgName : String := ".0"

/-- Builtins that CONSUME their argument on the spot, so a view handed to one
cannot outlive the call — which is what licenses the rewrite's snapshot. -/
def consumesViewArg : String → Bool
  | "list" | "tuple" | "set" | "sum" | "any" | "all" => true
  | "sorted" | "max" | "min" | "len" => true
  | _ => false
