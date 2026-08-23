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
  /-- `CompositeLit` over a named struct type, with `KeyValueExpr` fields.
  Keyed form only: 87% of real composite literals name their fields, and
  the positional form depends on declaration order, which is a typing
  question `go/types` answers and this walker does not. -/
  | structLit (typeName : String) (fields : List (String × Expr))
  /-- `SelectorExpr` reading a struct field. -/
  | field (e : Expr) (name : String)
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
  /-- `TypeSpec` over a struct type — 72.4% of type declarations
  (`docs/backlog/go.md` §G4). Records the field names in declaration
  order; interfaces are 3.9% and a later rung. -/
  | typeDecl (name : String) (fields : List String)
  /-- `ForStmt`, all three clauses optional.

  **This is where `LangVersion` stops being a predicate and becomes a
  branch** (`docs/backlog/go.md` §G4: the go1.21→1.22 delta touches
  21,715 sites in the standard library alone). And with all three clauses
  absent it is bare `for {}`, the commonest loop form at 47.0%, where
  fuel stops being a formality. -/
  | forS (init : Option Stmt) (cond : Option Expr) (post : Option Stmt)
         (body : List Stmt)
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

mutual

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
  | .structLit tname fields => do
      let w ← get
      match w.types.find? (fun p => p.1 == tname) with
      | none =>
          refuseGo .unsupportedConstruct (SpecRef.spec "Type_declarations")
            s!"composite literal of undeclared type '{tname}'"
      | some (_, declared) =>
          -- Every key must be a declared field. A literal naming a field
          -- the type does not have is a TYPE error in Go, and the walker
          -- refuses rather than inventing one.
          let keys := fields.map (·.1)
          if keys.any (fun k => !declared.contains k) then
            refuseGo .unsupportedConstruct (SpecRef.spec "Composite_literals")
              s!"literal names a field '{tname}' does not declare"
          else do
            -- Fields are evaluated by structural recursion over the
            -- literal (`evalFields`), THEN placed in declaration order.
            -- Evaluating them inside a walk over `declared` would lose
            -- the structural link and the definition would not be
            -- accepted — the termination argument shaping the code.
            let vals ← evalFields fields
            -- Absent fields take the zero value. Rung 2 carries no field
            -- types, so the zero is `nilV`; what it should be per type is
            -- a later rung's census.
            pure (.structV (declared.map (fun fn =>
              (fn, (vals.find? (fun p => p.1 == fn)).elim GoVal.nilV (·.2)))))
  | .field e fname => do
      match ← evalExpr e with
      | .structV fs =>
          match fs.find? (fun p => p.1 == fname) with
          | some (_, v) => pure v
          | none =>
              refuseGo .unsupportedConstruct (SpecRef.spec "Selectors")
                s!"no field '{fname}'"
      | _ =>
          refuseGo .unsupportedConstruct (SpecRef.spec "Selectors")
            "selector on a non-struct"
  | .binary op l r => do
      let lv ← evalExpr l
      let rv ← evalExpr r
      match lv, rv with
      | .intV k x, .intV _ y => binNum op k x y
      | .ptrV a, .ptrV b =>
          -- Go compares pointers with `==`: equal when they point at the
          -- same variable. This is what makes the go1.22 loop-var delta
          -- OBSERVABLE without closures — see `Spec.lean`.
          match op with
          | .eq => pure (.boolV (a == b))
          | .ne => pure (.boolV (a != b))
          | _ =>
              refuseGo .unsupportedConstruct (SpecRef.spec "Comparison_operators")
                "pointers admit only == and !="
      | .ptrV _, .nilV | .nilV, .ptrV _ =>
          match op with
          | .eq => pure (.boolV false)
          | .ne => pure (.boolV true)
          | _ =>
              refuseGo .unsupportedConstruct (SpecRef.spec "Comparison_operators")
                "pointers admit only == and !="
      | .nilV, .nilV =>
          match op with
          | .eq => pure (.boolV true)
          | .ne => pure (.boolV false)
          | _ =>
              refuseGo .unsupportedConstruct (SpecRef.spec "Comparison_operators")
                "nil admits only == and !="
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

/-- Evaluate a composite literal's fields, in source order. Structural on
the field list, which is what makes `evalExpr`'s literal arm terminate. -/
def evalFields : List (String × Expr) → GoM (List (String × GoVal))
  | [] => pure []
  | (n, e) :: rest => do
      let v ← evalExpr e
      let vs ← evalFields rest
      pure ((n, v) :: vs)

end

/-- Truthiness is NOT a Go concept: a condition must be a `bool`. Anything
else is a refusal rather than a coercion. -/
def asBool (v : GoVal) : GoM Bool :=
  match v with
  | .boolV b => pure b
  | _ =>
      refuseGo .unsupportedConstruct (SpecRef.spec "If_statements")
        "condition is not a boolean"

/-- Re-declare each named local at a FRESH address, carrying its current
value across. This is the whole of the go1.22 loop-variable rule.

The specification, "For statements with for clause": *"Each iteration has
its own separate declared variable (or variables) [Go 1.22]. The variable
used by the first iteration is declared by the init statement. The
variable used by each subsequent iteration is declared implicitly before
executing the post statement and initialized to the value of the previous
iteration's variable at that moment."*

Two halves, and the second is the one a model can pass the famous tests
without (`docs/go-charter.md` §3.3): fresh LOCATIONS per iteration, and
the previous iteration's VALUE copied into them. Freshen without copying
and every closure-capture test still passes while ordinary counting loops
silently break. -/
def freshenLoopVars : List String → GoM Unit
  | [] => pure ()
  | n :: rest => do
      let v ← loadAddr (← lookupLocal n)
      bindLocal n v
      freshenLoopVars rest

mutual

/-- Step one statement.

**Fuel is the recursion argument, and every nested step spends one.**
`LeanModels/Core/Outcome.lean` is explicit that fuel is an index on the
step function and never a monad layer, because hidden in state it is not
an argument and termination cannot be shown. Recursing on fuel alone —
rather than lexicographically on (fuel, statement) — makes that argument
trivial, and costs only that nesting depth draws on the same budget as
iteration. Exhaustion is `Halt.timeout` via Core's `exhausted`, and is
never a refusal. -/
def execStmt : Nat → Stmt → GoM Flow
  | 0, _ => LeanModels.exhausted
  | _ + 1, .empty => pure .normal
  | f + 1, .block body => execSeq f body
  | _ + 1, .expr e => do let _ ← evalExpr e; pure .normal
  | _ + 1, .declare name e => do bindLocal name (← evalExpr e); pure .normal
  | _ + 1, .assign name e => do storeLocal name (← evalExpr e); pure .normal
  | _ + 1, .incDec name inc => do
      let a ← lookupLocal name
      match ← loadAddr a with
      | .intV k n => do
          storeLocal name (GoVal.mkInt k (if inc then n + 1 else n - 1))
          pure .normal
      | _ =>
          refuseGo .unsupportedConstruct (SpecRef.spec "IncDec_statements")
            "++/-- on a non-integer"
  | _ + 1, .ret none => pure (.returned none)
  | _ + 1, .ret (some e) => do pure (.returned (some (← evalExpr e)))
  | f + 1, .ifS cond thenB elseB => do
      if ← asBool (← evalExpr cond) then execSeq f thenB else execSeq f elseB
  | f + 1, .labeled _ st => execStmt f st
  | _ + 1, .branch .break_ l => pure (.broke l)
  | _ + 1, .branch .continue_ l => pure (.continued l)
  | _ + 1, .branch .goto_ _ =>
      refuseGo .unsupportedConstruct (SpecRef.spec "Goto_statements")
        "goto needs a control-flow graph this walker does not build"
  | _ + 1, .branch .fallthrough_ _ =>
      -- DEFERRED AS ITS OWN RUNG, with a measured price: `fallthrough`
      -- appears in 208 of 5,186 switches — 4.0% (docs/backlog/go.md §G4).
      -- It is the one switch feature that breaks reading a case body as
      -- an independent block, because the body's exit depends on the NEXT
      -- clause. Deferring keeps 96% of switch sites reachable and keeps
      -- the rule compositional.
      refuseGo .unsupportedConstruct (SpecRef.spec "Fallthrough_statements")
        "fallthrough is deferred to its own rung (4.0% of switches)"
  | _ + 1, .typeDecl name fields => do
      modify (fun w => { w with types := (name, fields) :: w.types })
      pure .normal
  | f + 1, .forS init cond post body => do
      -- The loop variables live in a scope of their own, so the locals
      -- are saved and restored around the whole statement.
      let saved := (← get).locals
      match init with
      | some st => do let _ ← execStmt f st; pure ()
      | none => pure ()
      -- Whatever `init` declared IS the loop-variable set: the locals
      -- added since `saved`. Read off rather than guessed.
      let after := (← get).locals
      let loopVars := (after.take (after.length - saved.length)).map (·.1)
      let r ← execLoop f cond post body loopVars
      modify (fun w => { w with locals := saved })
      pure r
  | _ + 1, .unmodeled kind =>
      refuseGo .unsupportedConstruct (SpecRef.spec "Statements")
        s!"{kind} is in the census but not stepped yet"

/-- One turn of a `for`. Bare `for {}` — 47.0% of all `for` loops, the
commonest form — reaches this with `cond = none`, so nothing but fuel
bounds it, and it exhausts to `Halt.timeout`. -/
def execLoop : Nat → Option Expr → Option Stmt → List Stmt → List String → GoM Flow
  | 0, _, _, _, _ => LeanModels.exhausted
  | f + 1, cond, post, body, loopVars => do
      let proceed ← match cond with
        | none => pure true
        | some c => asBool (← evalExpr c)
      if !proceed then pure .normal else do
        let r ← execSeq f body
        match r with
        | .normal | .continued none => do
            -- THE VERSION BRANCH. Per-iteration scoping is go1.22 and
            -- later; before that the init statement's variables are
            -- re-used across iterations. One model, one rule, a branch
            -- on data carried per FILE — never two models.
            if (← get).lang.perIterationLoopVars then
              freshenLoopVars loopVars
            match post with
            | some st => do let _ ← execStmt f st; pure ()
            | none => pure ()
            execLoop f cond post body loopVars
        | .broke none => pure .normal
        | other => pure other

/-- Run a sequence, stopping at the first non-normal flow. -/
def execSeq : Nat → List Stmt → GoM Flow
  | 0, _ => LeanModels.exhausted
  | _ + 1, [] => pure .normal
  | f + 1, st :: rest => do
      match ← execStmt f st with
      | .normal => execSeq f rest
      | fl => pure fl

end

end LeanModels.Go
