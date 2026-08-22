import LeanModels.Go.Sem

/-!
# Rung 1's abstract syntax, and the first statement walker

M1 inch 1, third part. The syntax here is scoped by MEASUREMENT, not by
the specification: `docs/backlog/go.md` §G1 derived rung 1 as 45 `go/ast`
node kinds reaching 3,084 of the standard library's 5,419 files (56.9%),
and this file carries that vocabulary and refuses everything else by name.

## Why `return`/`break`/`continue` are in α and only `panic` is in ρ

The ES lane put all four of its abrupt completions in ρ, because ES2026
writes `? Foo(x)` — propagate ANY abrupt — at 2,328 sites, so `ExceptT`'s
bind IS the spec's operator. **Go's specification does not have that
operator**, and its four exits do not behave alike:

* `panic` unwinds *across frames*, running deferred functions at each one,
  and is observable by `recover` — that is `ExceptT` propagation, so it is
  ρ (`Sem.lean` states the clause).
* `return`, `break` and `continue` are ordinary structured control flow.
  They never cross a function boundary uninvited, they run no deferred
  work of their own, and `recover` cannot see them.

Putting the latter three in ρ would make every deferred-function rule have
to distinguish "a panic is in flight" from "a return is in flight", which
is precisely the distinction `recover` is defined by. So they are a `Flow`
in α — the Python tier's shape, adopted here because Go's control flow is
shaped like Python's and not like ES's.

## Fuel

Fuel is an explicit `Nat` parameter and exhaustion is `Halt.timeout` and
nothing else, never a refusal — the family's rule. Statement-level
recursion is structural, so fuel is needed only where the language admits
unbounded iteration.
-/

namespace LeanModels.Go

/-- Binary operators, scoped to rung 1's census
(`docs/go-construct-census.json`). -/
inductive BinOp where
  | add | sub | mul | quo | rem
  | eq | ne | lt | le | gt | ge
  | land | lor
  deriving Repr, DecidableEq, Inhabited

/-- `break` and `continue` — `BranchStmt` in the census. `goto` and
`fallthrough` are the same AST node in Go and are REFUSED rather than
guessed at, because both need a control-flow graph the walker does not
build at inch 1. -/
inductive BranchKind where
  | break_ | continue_ | goto_ | fallthrough_
  deriving Repr, DecidableEq, Inhabited

mutual

/-- Expressions, rung 1. -/
inductive Expr where
  /-- A literal — `BasicLit`, and the composite forms once they land. -/
  | lit (v : GoVal)
  /-- `Ident`. -/
  | ident (name : String)
  /-- `ParenExpr`. It is a NODE in `go/ast`, not sugar erased by the
  parser, so the model carries it: the census counts it and the extractor
  will emit it. -/
  | paren (e : Expr)
  /-- `BinaryExpr`. -/
  | binary (op : BinOp) (l r : Expr)
  /-- `UnaryExpr`, address-of. Rung 1's fixture takes `&local`. -/
  | addrOf (name : String)
  /-- `StarExpr` as an expression — a dereference. -/
  | deref (e : Expr)
  deriving Repr, Inhabited

/-- Statements, rung 1. -/
inductive Stmt where
  /-- `EmptyStmt`. Rare — 4 of the standard library's 5,419 files — and
  present because rung 1's vocabulary is exact. -/
  | empty
  /-- `BlockStmt`. -/
  | block (body : List Stmt)
  /-- `ExprStmt`. -/
  | expr (e : Expr)
  /-- `DeclStmt` — `var x = e`. Half of the rung's biggest single unlock:
  `DeclStmt` and `TypeSpec` together take coverage 31.1% → 56.9%. -/
  | declare (name : String) (e : Expr)
  /-- `AssignStmt`, in its single-target form. -/
  | assign (name : String) (e : Expr)
  /-- `IncDecStmt`. -/
  | incDec (name : String) (inc : Bool)
  /-- `ReturnStmt`. -/
  | ret (e : Option Expr)
  /-- `IfStmt`. -/
  | ifS (cond : Expr) (thenB : List Stmt) (elseB : List Stmt)
  /-- `LabeledStmt`. -/
  | labeled (label : String) (s : Stmt)
  /-- `BranchStmt`. -/
  | branch (kind : BranchKind) (label : Option String)
  /-- Anything in the census that inch 1 does not step. Carries the
  `go/ast` kind name so the refusal can name it — the envelope's
  `Unsupported` leaf, in the syntax rather than beside it. -/
  | unmodeled (astKind : String)
  deriving Repr, Inhabited

end

/-- How a statement sequence finished. `docs/statement-cookbook.md` §13's
short-circuit shape: a non-`normal` flow stops the sequence. -/
inductive Flow where
  | normal
  | returned (v : Option GoVal)
  | broke (label : Option String)
  | continued (label : Option String)
  deriving Repr, Inhabited

namespace Flow
/-- Whether a sequence may proceed to its next statement. -/
def isNormal : Flow → Bool
  | .normal => true
  | _ => false
end Flow

/-! ## The world's small operations -/

/-- Read an address. A read of an unbound address is a REFUSAL and not a
zero: Go has no uninitialised read to model, so reaching one means the
walker is wrong, and `docs/backlog.md`'s "never hide errors" says a wrong
walker must be loud. -/
def loadAddr (a : Addr) : GoM GoVal := do
  let w ← get
  match w.store.find? (fun p => p.1 == a) with
  | some (_, v) => pure v
  | none =>
      refuseGo .environment (SpecRef.spec "Variables")
        s!"read of unbound address {a}"

def lookupLocal (name : String) : GoM Addr := do
  let w ← get
  match w.locals.find? (fun p => p.1 == name) with
  | some (_, a) => pure a
  | none =>
      refuseGo .unsupportedConstruct (SpecRef.spec "Declarations_and_scope")
        s!"unbound identifier '{name}'"

/-- Bind a fresh address for `name` and store `v` there. -/
def bindLocal (name : String) (v : GoVal) : GoM Unit := do
  let w ← get
  let a := w.nextAddr
  set { w with
        nextAddr := a + 1,
        store := (a, v) :: w.store,
        locals := (name, a) :: w.locals }

/-- Write through an existing binding. -/
def storeLocal (name : String) (v : GoVal) : GoM Unit := do
  let a ← lookupLocal name
  let w ← get
  set { w with store := (a, v) :: w.store.filter (fun p => p.1 != a) }

/-! ## Arithmetic — one rule for both signednesses

`docs/go-charter.md`'s zero-UB finding, made operational. The Go
specification's "Integer overflow" defines BOTH cases, so `IntKind.wrap`
is the whole story and there is no arm that refuses. Division by zero is
a run-time PANIC (a defined outcome), not undefined behaviour, so it goes
to ρ. -/

def binNum (op : BinOp) (k : IntKind) (x y : Int) : GoM GoVal :=
  match op with
  | .add => pure (GoVal.mkInt k (x + y))
  | .sub => pure (GoVal.mkInt k (x - y))
  | .mul => pure (GoVal.mkInt k (x * y))
  | .quo =>
      if y = 0 then
        -- "Run-time panics": integer divide by zero panics. A DEFINED
        -- outcome, so ρ — never `undefined`.
        panicWith 0 (.stringV "runtime error: integer divide by zero")
      else pure (GoVal.mkInt k (x / y))
  | .rem =>
      if y = 0 then
        panicWith 0 (.stringV "runtime error: integer divide by zero")
      else pure (GoVal.mkInt k (x % y))
  | .eq => pure (.boolV (x == y))
  | .ne => pure (.boolV (x != y))
  | .lt => pure (.boolV (x < y))
  | .le => pure (.boolV (x ≤ y))
  | .gt => pure (.boolV (x > y))
  | .ge => pure (.boolV (x ≥ y))
  | .land | .lor =>
      refuseGo .unsupportedConstruct (SpecRef.spec "Logical_operators")
        "logical operator applied to integers"

/-- Evaluate an expression. Structural: no fuel needed. -/
def evalExpr : Expr → GoM GoVal
  | .lit v => pure v
  | .ident name => do loadAddr (← lookupLocal name)
  | .paren e => evalExpr e
  | .addrOf name => do pure (.ptrV (← lookupLocal name))
  | .deref e => do
      match ← evalExpr e with
      | .ptrV a => loadAddr a
      | _ =>
          refuseGo .unsupportedConstruct (SpecRef.spec "Address_operators")
            "dereference of a non-pointer"
  | .binary op l r => do
      let lv ← evalExpr l
      let rv ← evalExpr r
      match lv, rv with
      | .intV k x, .intV _ y => binNum op k x y
      | .boolV a, .boolV b =>
          match op with
          | .land => pure (.boolV (a && b))
          | .lor => pure (.boolV (a || b))
          | .eq => pure (.boolV (a == b))
          | .ne => pure (.boolV (a != b))
          | _ =>
              refuseGo .unsupportedConstruct (SpecRef.spec "Logical_operators")
                "arithmetic operator applied to booleans"
      | _, _ =>
          refuseGo .unsupportedConstruct (SpecRef.spec "Operators")
            "operands outside rung 1's value vocabulary"

/-- Truthiness is NOT a Go concept: a condition must be a `bool`. Anything
else is a refusal rather than a coercion. -/
def asBool (v : GoVal) : GoM Bool :=
  match v with
  | .boolV b => pure b
  | _ =>
      refuseGo .unsupportedConstruct (SpecRef.spec "If_statements")
        "condition is not a boolean"

mutual

/-- Step one statement. -/
def execStmt (fuel : Nat) : Stmt → GoM Flow
  | .empty => pure .normal
  | .block body => execSeq fuel body
  | .expr e => do let _ ← evalExpr e; pure .normal
  | .declare name e => do bindLocal name (← evalExpr e); pure .normal
  | .assign name e => do storeLocal name (← evalExpr e); pure .normal
  | .incDec name inc => do
      let a ← lookupLocal name
      match ← loadAddr a with
      | .intV k n => do storeLocal name (GoVal.mkInt k (if inc then n + 1 else n - 1)); pure .normal
      | _ =>
          refuseGo .unsupportedConstruct (SpecRef.spec "IncDec_statements")
            "++/-- on a non-integer"
  | .ret none => pure (.returned none)
  | .ret (some e) => do pure (.returned (some (← evalExpr e)))
  | .ifS cond thenB elseB => do
      if ← asBool (← evalExpr cond) then execSeq fuel thenB else execSeq fuel elseB
  | .labeled _ s => execStmt fuel s
  | .branch .break_ l => pure (.broke l)
  | .branch .continue_ l => pure (.continued l)
  | .branch .goto_ _ =>
      refuseGo .unsupportedConstruct (SpecRef.spec "Goto_statements")
        "goto needs a control-flow graph the inch-1 walker does not build"
  | .branch .fallthrough_ _ =>
      refuseGo .unsupportedConstruct (SpecRef.spec "Fallthrough_statements")
        "fallthrough is a switch-body rule and switch is not stepped at inch 1"
  | .unmodeled kind =>
      refuseGo .unsupportedConstruct (SpecRef.spec "Statements")
        s!"{kind} is in rung 1's vocabulary but not stepped at inch 1"

/-- Run a sequence, stopping at the first non-normal flow. -/
def execSeq (fuel : Nat) : List Stmt → GoM Flow
  | [] => pure .normal
  | s :: rest => do
      match ← execStmt fuel s with
      | .normal => execSeq fuel rest
      | f => pure f

end

end LeanModels.Go
