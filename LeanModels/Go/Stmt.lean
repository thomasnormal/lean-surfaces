import LeanModels.Go.Sem
import LeanModels.Go.Obs

/-!
# The abstract syntax and the statement walker

The syntax here is scoped by MEASUREMENT, not by the specification, and
the scope has GROWN past the rung it started at. An audit
(`docs/quality-audit-2026-08-23.md`) caught this header still quoting
rung 1's figures after three inches had widened it; the current state:

| inch | added |
| --- | --- |
| 1 (§G2) | rung 1's 45 `go/ast` kinds |
| 2 (§G5) | struct declarations, the go1.22 loop-var branch, bare-`for` fuel |
| 3 (§G6) | **calls**, compound assignment, shifts |
| 4 (§G7) | — (census + the exemplar's spec half) |
| 5 (§G15) | string indexing and conversions; strings became BYTES |
| 6 (§G18) | **slices**: `a[i:j]`, `len`/`cap`, indexed assignment, the header value model |
| 7 (§G19) | `range` over a slice — desugared to `forS`, not a second loop |

**Do not quote a reach figure here.** Two earlier versions of this header
carried one and both went stale, and §G19 found the second was not even
reproducible: it was computed against an unrecorded vocabulary that
counted `SelectorExpr` as steppable, which this walker refuses (§G8).
Reach is now a RUN, not a docstring —

    harness/go/census.sh --reach $(go env GOROOT)/src

— whose vocabulary list is transcribed from the `Expr`/`Stmt`
constructors below and must be widened in the same commit that widens
them. Anything outside that vocabulary is refused by name rather than
guessed at.

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
  /-- Shifts. Added because the SUITE asked: the rung-3 exemplar
  `crypto/internal/bigmod.bitLen` is `n >>= 1`. A tier that picks its own
  operators picks the ones its fixtures need; picking from the corpus
  means picking the ones real code uses. The bitwise `&`/`|`/`^`/`&^`
  family is NOT added here — no exemplar needed it yet, and declaring an
  operator the walker refuses would be a vocabulary claim the tier cannot
  honour. -/
  | shl | shr
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
  /-- A **CONVERSION**, `T(e)`.

  Go's grammar spells a conversion exactly like a call, and `go/ast` gives
  both a `CallExpr` — but they are different constructs, and
  `docs/backlog/go.md` §G14 measured the cost of conflating them: 51,255
  of the standard library's plain-identifier "calls" are conversions to a
  predeclared type, 26.3% of them, and bucketing those as `environment`
  put language work in the library's bucket.

  **The disambiguation is the FRONTEND's job**, which is what
  `docs/go-charter.md` §7.3 already rules for everything type-dependent:
  the extractor sees the predeclared name (`isBuiltinTypeName`) and emits
  this node. Keeping it a separate constructor also keeps `evalExpr`'s
  `.call` arm thin — inlining the check there was measured to time out
  four of the exemplar's proofs. -/
  | convert (typeName : String) (e : Expr)
  /-- `IndexExpr`. At this rung the operand is a STRING, and Go's rule is
  that `s[i]` yields a **byte** — never a rune, and never a character.
  Arrays, slices and maps are later rungs (`docs/backlog/go.md` §G14
  measured the split: slices are 85.4% of `ArrayType`, fixed arrays
  14.6%). -/
  | index (x i : Expr)
  /-- `SliceExpr` — `a[lo:hi]`. A NEW HEADER over the SAME backing array:
  that sharing is the whole content of the rung
  (`docs/backlog/go.md` §G17). -/
  | slice (x : Expr) (lo hi : Option Expr)
  /-- `len(e)` / `cap(e)`. A dedicated node rather than a branch inside
  `.call`, for the reason §G15 measured: inlining a name check there made
  `simp only [evalExpr]` carry it through every reduction and timed out
  four proofs. The frontend emits this. -/
  | builtin1 (name : String) (e : Expr)
  /-- `CallExpr` on a plain identifier. **The single biggest reach unlock
  in the census**: calls appear in 73.3% of the files rung 1 already
  reaches (`docs/backlog/go.md` §G6), so without them nothing with a
  function in it runs. Method calls and calls through values need
  `go/types` and are a later rung. -/
  | call (name : String) (args : List Expr)
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
  /-- `AssignStmt` in its compound form — `x op= e`. The census's
  exemplar needs `>>=`; the form is general. -/
  | assignOp (op : BinOp) (name : String) (e : Expr)
  /-- `a[i] = e` — a write THROUGH a slice, into its backing array. This
  is the statement the aliasing rows of the acceptance case turn on. -/
  | assignIndex (x i e : Expr)
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
  /-- `RangeStmt` over a SLICE — `for k, v := range s`.

  **Desugared to `forS`, not forked.** `docs/backlog/go.md` §G17 sized
  this rung with the note that `range` should reuse the loop machinery the
  `bitLen` induction is proved about, and desugaring is the strongest form
  of that: this arm builds a three-clause `for` and calls `execStmt` on
  it, so there is no second loop implementation to keep in step and no
  second version-branch to get wrong — `execLoop`'s go1.22 freshening
  applies to the range variable for free, because it IS the init
  statement's variable. -/
  | rangeS (key : Option String) (val : Option String) (x : Expr) (body : List Stmt)
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

/-- Read element `k` of the backing array at `a`. Out of range is a
run-time PANIC — a defined outcome, never `undefined`. -/
def loadIdx (a : Addr) (k : Nat) : GoM GoVal := do
  match ← loadAddr a with
  | .arrayV elems =>
      match elems[k]? with
      | some v => pure v
      | none => panicWith 0 (GoVal.runtimeErrorV "runtime error: index out of range")
  | _ =>
      refuseGo .unsupportedConstruct (SpecRef.spec "Index_expressions")
        "indexed a non-array backing object"

/-- Write element `k` of the backing array at `a`. **This is where
aliasing happens**: every slice header pointing at `a` sees it. -/
def storeIdx (a : Addr) (k : Nat) (v : GoVal) : GoM Unit := do
  match ← loadAddr a with
  | .arrayV elems =>
      if k < elems.length then do
        let w ← get
        set { w with store := (a, .arrayV (elems.set k v)) :: w.store.filter (fun p => p.1 != a) }
      else panicWith 0 (GoVal.runtimeErrorV "runtime error: index out of range")
  | _ =>
      refuseGo .unsupportedConstruct (SpecRef.spec "Index_expressions")
        "indexed a non-array backing object"

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
        panicWith 0 (GoVal.runtimeErrorV "runtime error: integer divide by zero")
      else pure (GoVal.mkInt k (x / y))
  | .rem =>
      if y = 0 then
        panicWith 0 (GoVal.runtimeErrorV "runtime error: integer divide by zero")
      else pure (GoVal.mkInt k (x % y))
  | .eq => pure (.boolV (x == y))
  | .ne => pure (.boolV (x != y))
  | .lt => pure (.boolV (x < y))
  | .le => pure (.boolV (x ≤ y))
  | .gt => pure (.boolV (x > y))
  | .ge => pure (.boolV (x ≥ y))
  | .shl | .shr =>
      -- "Arithmetic operators": the shift count must be non-negative, and
      -- a negative count at run time is a run-time PANIC — a DEFINED
      -- outcome, so ρ. Another instance of the zero-UB posture: C leaves
      -- this undefined, Go names the panic.
      if y < 0 then
        panicWith 0 (GoVal.runtimeErrorV "runtime error: negative shift amount")
      else
        let p : Int := 2 ^ y.toNat
        match op with
        | .shl => pure (GoVal.mkInt k (x * p))
        -- `>>` is an ARITHMETIC shift: it floors, so that it agrees with
        -- division by a power of two on negatives too. `Int./` truncates
        -- toward zero and would be wrong there; `fdiv` floors.
        | _ => pure (GoVal.mkInt k (Int.fdiv x p))
  | .land | .lor =>
      refuseGo .unsupportedConstruct (SpecRef.spec "Logical_operators")
        "logical operator applied to integers"

/-- The predeclared TYPE names.

**`int(x)` parses as a `CallExpr` on an `Ident`** — syntactically
identical to a call to a function named `int` — and only `go/types` can
tell the two apart in general. The predeclared names are the one case a
tier can separate without a type checker, and separating them is not
cosmetic: a conversion is a LANGUAGE CONSTRUCT (retires by climbing a
rung) while a missing function is `environment` (retires by widening the
modelled slice), and `docs/family-architecture.md` §5.2 requires the two
be reported separately.

Measured: **51,255 of the standard library's plain-identifier calls are
conversions to a predeclared type — 26.3% of them.** Before this list
they were every one of them bucketed as `environment`. -/
def isBuiltinTypeName (s : String) : Bool :=
  s == "bool" || s == "byte" || s == "complex64" || s == "complex128" ||
  s == "error" || s == "float32" || s == "float64" || s == "int" ||
  s == "int8" || s == "int16" || s == "int32" || s == "int64" ||
  s == "rune" || s == "string" || s == "uint" || s == "uint8" ||
  s == "uint16" || s == "uint32" || s == "uint64" || s == "uintptr" ||
  s == "any"

/-- Convert a value to a predeclared integer type. The result is reduced
into the target's range by the target's own rule — which is
`IntKind.wrap`, the same one function the spec gives for both
signednesses (`docs/go-charter.md`'s zero-UB finding). -/
def convertInt (name : String) (v : GoVal) : Option GoVal :=
  match v with
  | .intV _ n =>
      match name with
      | "int"     => some (GoVal.mkInt IntKind.int64 n)
      | "int64"   => some (GoVal.mkInt IntKind.int64 n)
      | "int32"   => some (GoVal.mkInt IntKind.int32 n)
      | "int16"   => some (GoVal.mkInt IntKind.int16 n)
      | "int8"    => some (GoVal.mkInt IntKind.int8 n)
      | "uint"    => some (GoVal.mkInt IntKind.uint64 n)
      | "uint64"  => some (GoVal.mkInt IntKind.uint64 n)
      | "uint32"  => some (GoVal.mkInt IntKind.uint32 n)
      | "uint16"  => some (GoVal.mkInt IntKind.uint16 n)
      | "uint8"   => some (GoVal.mkInt IntKind.uint8 n)
      | "byte"    => some (GoVal.mkInt IntKind.uint8 n)
      | _ => none
  | _ => none

/-- Bind a call's parameters in the callee's frame. -/
def bindParams : List String → List GoVal → GoM Unit
  | [], _ => pure ()
  | _, [] => pure ()
  | n :: ns, v :: vs => do bindLocal n v; bindParams ns vs

/-- A program's function table: name to (parameter names, body).

**Program text, not world state.** `GoWorld` is declared before `Stmt`
and so cannot mention it, but the deeper reason is that a function table
does not change as a program runs — threading it as a parameter says so,
and keeps `GoWorld` about the things that do move. -/
abbrev FuncTable := List (String × List String × List Stmt)

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

/-- Evaluate an expression.

**Fuel reaches expressions at this rung, and calls are why.** Until now
expression evaluation was structural and total; a call can recur, so the
argument that `evalExpr` terminates is now the same fuel argument the
statements use. Nothing else changed about it. -/
def evalExpr (prog : FuncTable) : Nat → Expr → GoM GoVal
  | 0, _ => LeanModels.exhausted
  | _ + 1, .lit v => pure v
  | _ + 1, .ident name => do loadAddr (← lookupLocal name)
  | f + 1, .paren e => evalExpr prog f e
  | _ + 1, .addrOf name => do pure (.ptrV (← lookupLocal name))
  | f + 1, .deref e => do
      match ← evalExpr prog f e with
      | .ptrV a => loadAddr a
      | _ =>
          refuseGo .unsupportedConstruct (SpecRef.spec "Address_operators")
            "dereference of a non-pointer"
  | f + 1, .structLit tname fields => do
      let w ← get
      match w.types.find? (fun p => p.1 == tname) with
      | none =>
          refuseGo .unsupportedConstruct (SpecRef.spec "Type_declarations")
            s!"composite literal of undeclared type '{tname}'"
      | some (_, declared) =>
          let keys := fields.map (·.1)
          if keys.any (fun k => !declared.contains k) then
            refuseGo .unsupportedConstruct (SpecRef.spec "Composite_literals")
              s!"literal names a field '{tname}' does not declare"
          else do
            let vals ← evalFields prog f fields
            pure (.structV (declared.map (fun fn =>
              (fn, (vals.find? (fun p => p.1 == fn)).elim GoVal.nilV (·.2)))))
  | f + 1, .field e fname => do
      match ← evalExpr prog f e with
      | .structV fs =>
          match fs.find? (fun p => p.1 == fname) with
          | some (_, v) => pure v
          | none =>
              refuseGo .unsupportedConstruct (SpecRef.spec "Selectors")
                s!"no field '{fname}'"
      | _ =>
          refuseGo .unsupportedConstruct (SpecRef.spec "Selectors")
            "selector on a non-struct"
  | f + 1, .convert tname e => do
      match convertInt tname (← evalExpr prog f e) with
      | some v => pure v
      | none =>
          refuseGo .unsupportedConstruct (SpecRef.spec "Conversions")
            s!"conversion to '{tname}' is not stepped yet"
  | f + 1, .builtin1 name e => do
      match name, ← evalExpr prog f e with
      | "len", .sliceV _ _ l _   => pure (GoVal.mkInt IntKind.int64 (l : Int))
      | "cap", .sliceV _ _ _ c   => pure (GoVal.mkInt IntKind.int64 (c : Int))
      | "len", .stringV bs       => pure (GoVal.mkInt IntKind.int64 (bs.length : Int))
      | _, _ =>
          refuseGo .unsupportedConstruct (SpecRef.spec "Length_and_capacity")
            s!"{name} of an operand outside this rung"
  | f + 1, .slice x lo hi => do
      match ← evalExpr prog f x with
      | .sliceV b off l c => do
          -- Defaults: a missing low is 0, a missing high is the LENGTH
          -- (not the capacity) — the spec's rule, and the difference is
          -- exactly what the acceptance case's fourth row turns on.
          let lo' ← match lo with
            | none => pure 0
            | some e => match ← evalExpr prog f e with
                        | .intV _ n => pure n.toNat
                        | _ => pure 0
          let hi' ← match hi with
            | none => pure l
            | some e => match ← evalExpr prog f e with
                        | .intV _ n => pure n.toNat
                        | _ => pure l
          if lo' ≤ hi' && hi' ≤ c then
            -- The new header points at the SAME backing array. `cap`
            -- shrinks from the low end only, which is why it can reach
            -- past the new length.
            pure (.sliceV b (off + lo') (hi' - lo') (c - lo'))
          else
            panicWith 0 (GoVal.runtimeErrorV "runtime error: slice bounds out of range")
      | _ =>
          refuseGo .unsupportedConstruct (SpecRef.spec "Slice_expressions")
            "slice expression outside this rung (slices only)"
  | f + 1, .index x i => do
      match ← evalExpr prog f x, ← evalExpr prog f i with
      | .sliceV b off l _, .intV _ n =>
          if n < 0 || n.toNat ≥ l then
            panicWith 0 (GoVal.runtimeErrorV "runtime error: index out of range")
          else loadIdx b (off + n.toNat)
      | .stringV bytes, .intV _ n =>
          if n < 0 then
            -- "Index expressions": a negative or out-of-range index is a
            -- run-time PANIC, a DEFINED outcome — never undefined.
            panicWith 0 (GoVal.runtimeErrorV "runtime error: index out of range")
          else
            match bytes[n.toNat]? with
            | some b => pure (.intV IntKind.uint8 (b.toNat : Int))
            | none =>
                panicWith 0 (GoVal.runtimeErrorV "runtime error: index out of range")
      | _, _ =>
          refuseGo .unsupportedConstruct (SpecRef.spec "Index_expressions")
            "indexing outside this rung (string only)"
  | f + 1, .call name args => do
      match prog.find? (fun d => d.1 == name) with
      | none =>
          -- A call to something the program does not declare is
          -- ENVIRONMENT: it retires by widening the modelled slice, never
          -- by climbing a rung. **Conversions do not reach here** — they
          -- are `Expr.convert`, emitted by the frontend.
          refuseGo .environment (SpecRef.spec "Calls") s!"undefined: {name}"
      | some (_, params, body) =>
          if params.length != args.length then
            refuseGo .unsupportedConstruct (SpecRef.spec "Calls")
              s!"{name}: wrong argument count"
          else do
            -- Arguments are evaluated in the CALLER's frame, before any
            -- parameter is bound — the spec's order, and it matters when
            -- an argument names a variable the callee also has.
            let vals ← evalArgs prog f args
            let saved := (← get).locals
            bindParams params vals
            let r ← execSeq prog f body
            modify (fun w => { w with locals := saved })
            match r with
            | .returned (some v) => pure v
            -- A bare `return`, or falling off the end, yields no value.
            -- Rung 3 has single-valued functions only, so `nilV` is the
            -- honest answer and a caller that uses it will refuse on the
            -- type mismatch rather than silently read a zero.
            | .returned none | .normal => pure GoVal.nilV
            | _ =>
                refuseGo .unsupportedConstruct (SpecRef.spec "Calls")
                  s!"{name}: break or continue crossed a function boundary"
  | f + 1, .binary op l r => do
      let lv ← evalExpr prog f l
      let rv ← evalExpr prog f r
      match lv, rv with
      | .intV k x, .intV _ y => binNum op k x y
      | .ptrV a, .ptrV b =>
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
            "operands outside this rung's value vocabulary"

/-- Composite-literal fields, in source order. -/
def evalFields (prog : FuncTable) : Nat → List (String × Expr) →
    GoM (List (String × GoVal))
  | _, [] => pure []
  | 0, _ => LeanModels.exhausted
  | f + 1, (n, e) :: rest => do
      let v ← evalExpr prog f e
      let vs ← evalFields prog f rest
      pure ((n, v) :: vs)

/-- Call arguments, left to right. -/
def evalArgs (prog : FuncTable) : Nat → List Expr → GoM (List GoVal)
  | _, [] => pure []
  | 0, _ => LeanModels.exhausted
  | f + 1, e :: rest => do
      let v ← evalExpr prog f e
      let vs ← evalArgs prog f rest
      pure (v :: vs)

/-- Step one statement. Fuel is the recursion argument and every nested
step spends one. -/
def execStmt (prog : FuncTable) : Nat → Stmt → GoM Flow
  | 0, _ => LeanModels.exhausted
  | _ + 1, .empty => pure .normal
  | f + 1, .block body => execSeq prog f body
  | f + 1, .expr e => do let _ ← evalExpr prog f e; pure .normal
  | f + 1, .declare name e => do bindLocal name (← evalExpr prog f e); pure .normal
  | f + 1, .assign name e => do storeLocal name (← evalExpr prog f e); pure .normal
  | f + 1, .assignOp op name e => do
      let cur ← loadAddr (← lookupLocal name)
      let rhs ← evalExpr prog f e
      match cur, rhs with
      | .intV k x, .intV _ y => do
          storeLocal name (← binNum op k x y); pure .normal
      | _, _ =>
          refuseGo .unsupportedConstruct (SpecRef.spec "Assignment_statements")
            "compound assignment outside the integer vocabulary"
  | _ + 1, .incDec name inc => do
      let a ← lookupLocal name
      match ← loadAddr a with
      | .intV k n => do
          storeLocal name (GoVal.mkInt k (if inc then n + 1 else n - 1))
          pure .normal
      | _ =>
          refuseGo .unsupportedConstruct (SpecRef.spec "IncDec_statements")
            "++/-- on a non-integer"
  | f + 1, .assignIndex x i e => do
      match ← evalExpr prog f x, ← evalExpr prog f i with
      | .sliceV b off l _, .intV _ n =>
          if n < 0 || n.toNat ≥ l then
            panicWith 0 (GoVal.runtimeErrorV "runtime error: index out of range")
          else do
            storeIdx b (off + n.toNat) (← evalExpr prog f e)
            pure .normal
      | _, _ =>
          refuseGo .unsupportedConstruct (SpecRef.spec "Assignment_statements")
            "indexed assignment outside this rung (slices only)"
  | _ + 1, .ret none => pure (.returned none)
  | f + 1, .ret (some e) => do pure (.returned (some (← evalExpr prog f e)))
  | f + 1, .ifS cond thenB elseB => do
      if ← asBool (← evalExpr prog f cond) then execSeq prog f thenB
      else execSeq prog f elseB
  | f + 1, .labeled _ st => execStmt prog f st
  | _ + 1, .branch .break_ l => pure (.broke l)
  | _ + 1, .branch .continue_ l => pure (.continued l)
  | _ + 1, .branch .goto_ _ =>
      refuseGo .unsupportedConstruct (SpecRef.spec "Goto_statements")
        "goto needs a control-flow graph this walker does not build"
  | _ + 1, .branch .fallthrough_ _ =>
      -- DEFERRED AS ITS OWN RUNG, at a measured 4.0% of switches
      -- (docs/backlog/go.md §G4).
      refuseGo .unsupportedConstruct (SpecRef.spec "Fallthrough_statements")
        "fallthrough is deferred to its own rung (4.0% of switches)"
  | _ + 1, .typeDecl name fields => do
      modify (fun w => { w with types := (name, fields) :: w.types })
      pure .normal
  | f + 1, .forS init cond post body => do
      let saved := (← get).locals
      match init with
      | some st => do let _ ← execStmt prog f st; pure ()
      | none => pure ()
      let after := (← get).locals
      let loopVars := (after.take (after.length - saved.length)).map (·.1)
      let r ← execLoop prog f cond post body loopVars
      modify (fun w => { w with locals := saved })
      pure r
  | f + 1, .rangeS key val x body => do
      -- "For statements with range clause": the range expression is
      -- evaluated ONCE. Capturing the header in a literal is that.
      match ← evalExpr prog f x with
      | .sliceV b off l c => do
          -- THE COUNTER IS HIDDEN, and that is not a detail. Desugaring
          -- to `for i := 0; i < len(s); i++` with the RANGE VARIABLE as
          -- the counter is wrong, and `gc` says so: a body that assigns
          -- to `i` ends that loop early, while `range` iterates the full
          -- length regardless. Measured (go1.25.6 darwin/arm64), body
          -- `n++; i = 100` over a 5-element slice:
          --
          --     for i := range s          -> 5 iterations
          --     for i := 0; i < len(s); i++ -> 1 iteration
          --
          -- So the counter gets a name no Go program can write, and the
          -- range variables are DECLARED FROM it at the top of each
          -- iteration. Assignments to them are then discarded by the next
          -- iteration's declaration, which is exactly Go's behaviour.
          --
          -- This also removes the version question rather than answering
          -- it: go1.21 shares one `i` across iterations and go1.22 makes
          -- it per-iteration, but the difference is observable only by
          -- capturing `i` in a closure, and `FuncLit` is not in this
          -- walker's vocabulary. Declaring per iteration is correct for
          -- both at the constructs this rung admits.
          let idx := "«range»"
          let hdr : GoVal := .sliceV b off l c
          let bindKey : List Stmt := match key with
            | none => []
            | some k => [Stmt.declare k (.ident idx)]
          let bindVal : List Stmt := match val with
            | none => []
            | some v => [Stmt.declare v (.index (.lit hdr) (.ident idx))]
          let body' := bindKey ++ bindVal ++ body
          execStmt prog f
            (.forS (some (.declare idx (.lit (GoVal.mkInt IntKind.int64 0))))
                   (some (.binary .lt (.ident idx)
                          (.lit (GoVal.mkInt IntKind.int64 (l : Int)))))
                   (some (.incDec idx true))
                   body')
      | _ =>
          refuseGo .unsupportedConstruct (SpecRef.spec "For_statements")
            "range over an operand outside this rung (slices only)"
  | _ + 1, .unmodeled kind =>
      refuseGo .unsupportedConstruct (SpecRef.spec "Statements")
        s!"{kind} is in the census but not stepped yet"

/-- One turn of a `for`. Bare `for {}` reaches this with `cond = none`, so
nothing but fuel bounds it. -/
def execLoop (prog : FuncTable) :
    Nat → Option Expr → Option Stmt → List Stmt → List String → GoM Flow
  | 0, _, _, _, _ => LeanModels.exhausted
  | f + 1, cond, post, body, loopVars => do
      let proceed ← match cond with
        | none => pure true
        | some c => asBool (← evalExpr prog f c)
      if !proceed then pure .normal else do
        let r ← execSeq prog f body
        match r with
        | .normal | .continued none => do
            -- THE VERSION BRANCH: per-iteration scoping is go1.22+.
            if (← get).lang.perIterationLoopVars then
              freshenLoopVars loopVars
            match post with
            | some st => do let _ ← execStmt prog f st; pure ()
            | none => pure ()
            execLoop prog f cond post body loopVars
        | .broke none => pure .normal
        | other => pure other

/-- Run a sequence, stopping at the first non-normal flow. -/
def execSeq (prog : FuncTable) : Nat → List Stmt → GoM Flow
  | 0, _ => LeanModels.exhausted
  | _ + 1, [] => pure .normal
  | f + 1, st :: rest => do
      match ← execStmt prog f st with
      | .normal => execSeq prog f rest
      | fl => pure fl

end

/-- Call a top-level function by name with already-evaluated arguments —
the entry point a fixture uses. -/
def callFunction (prog : FuncTable) (fuel : Nat) (name : String)
    (args : List GoVal) : GoM GoVal := do
  match prog.find? (fun d => d.1 == name) with
  | none => refuseGo .environment (SpecRef.spec "Calls") s!"undefined: {name}"
  | some (_, params, body) =>
      if params.length != args.length then
        refuseGo .unsupportedConstruct (SpecRef.spec "Calls")
          s!"{name}: wrong argument count"
      else do
        let saved := (← get).locals
        bindParams params args
        let r ← execSeq prog fuel body
        modify (fun w => { w with locals := saved })
        match r with
        | .returned (some v) => pure v
        | .returned none | .normal => pure GoVal.nilV
        | _ =>
            refuseGo .unsupportedConstruct (SpecRef.spec "Calls")
              s!"{name}: break or continue crossed a function boundary"

end LeanModels.Go
