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
`lt` ↔ `Lt`, `ltE` ↔ `LtE`, `gt` ↔ `Gt`, `gtE` ↔ `GtE`. -/
inductive CmpOp where
  | eq | notEq | lt | ltE | gt | gtE
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

/-- A function parameter: schema `param` = `{"arg": …, "span": …}`. -/
structure Param where
  arg : String
  span : Span
deriving Repr, Inhabited, BEq, DecidableEq

/-- Expressions. Constructor ↔ schema `kind` mapping:
`constant` ↔ `Constant`, `name` ↔ `Name`, `binOp` ↔ `BinOp`,
`unaryOp` ↔ `UnaryOp`, `boolOp` ↔ `BoolOp`, `compare` ↔ `Compare`,
`call` ↔ `Call`, `list` ↔ `List`, `tuple` ↔ `Tuple`,
`subscript` ↔ `Subscript`, `unsupported` ↔ `Unsupported`. -/
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
  | unsupported (pyKind : String) (text : String) (span : Span)
deriving Repr, Inhabited, BEq
-- DecidableEq deriving does not cope with the nested `Array Expr`; derived BEq suffices.

/-- Statements. Constructor ↔ schema `kind` mapping (Lean-keyword-safe names):
`ret` ↔ `Return`, `assign` ↔ `Assign`, `augAssign` ↔ `AugAssign`,
`whileLoop` ↔ `While`, `ifStmt` ↔ `If`, `exprStmt` ↔ `Expr`,
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
was non-null (defaults / `*args` / kw-only / `**kwargs` / decorators), in which
case calling the function is `unsupported`. Plain positional params are always
listed in `params`. -/
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
  body : Array Stmt
  span : Span
deriving Repr, Inhabited, BEq
-- No DecidableEq: `Stmt` has none (nested arrays).

/-- A Python module: `def`s split out into `functions` (in source order);
all other top-level statements recorded in `topLevel` (in source order),
which v0 `callFunction` ignores (no globals / module init effects). -/
structure Module where
  functions : Array FunctionDefn
  topLevel : Array Stmt
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

/-- Python runtime errors representable in v0. Canonical harness names:
`TypeError`, `NameError`, `ZeroDivisionError`, `IndexError`, `ValueError`. -/
inductive PyErr where
  | typeError (msg : String)
  | nameError (name : String)
  | zeroDivisionError
  | indexError
  | valueError (msg : String)
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

/-- Local environments. First match wins on lookup; `Env.set` (later phase)
replaces in place, else appends. -/
abbrev Env := List (String × Val)

end LeanModels.Python
