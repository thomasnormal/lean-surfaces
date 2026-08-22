import LeanModels.C.C23.Memory

/-!
# §6.5 Expressions — the evaluator — M2 inch 3

C23 (N3220) §6.5, subclause by subclause. Citations follow
`docs/c23-spec-mirror.md`; refusals name their Annex J.2 index.

## FUEL'S FATE, decided BEFORE this file was written

The family checklist's step 7 (`docs/family-architecture.md` §8.4) makes
this a decision about the interpreter's TYPE, not a proof-layer choice
deferrable to later. **This layer is FUEL-FREE**: `evalExpr` is
STRUCTURALLY recursive on `Expr`, and calls enter through a HANDLER
parameter, which is where fuel arrives at inch 5.

Measured, on the shipped corpus:

| | |
| --- | ---: |
| full expressions | 1169 |
| …containing a call | 298 |
| **…CALL-FREE — the fuel-free fragment** | **871 (74.5%)** |

Three reasons this is the right cut:

1. **The fuel-free fragment is the majority of the corpus**, and the
   checklist gives that fragment the shared `mvcgen` and ~120 lines of
   `@[spec]` while the fuel-recursive points get the tier's own threshold
   assembly. Making the expression layer fuel-free maximizes the half
   that is cheap.
2. **This tier wants kernel-reducible runs.** Inch 2 shipped 50 `#guard`s
   and inch 6's scorer must RUN programs; structural recursion delivers
   that with no fuel argument to pick.
3. It is what `docs/c-semantics-design.md` §4.2 already required —
   *"every helper the interpreter computes with is STRUCTURAL
   recursion."*

So the fuel parameter does not appear here and is not owed here. The
`∃ n, ∀ fuel ≥ n` threshold form is assembled AROUND this layer, never
inside it.

**Where fuel DOES arrive, measured — and it is two places, not one.**
Inch 4's census corrected this file's first draft, which said "inch 5,
with calls":

* **Inch 4, with LOOPS.** The corpus has **84 loops** (50 `for`, 29 `do`,
  5 `while`), and an iteration count is not structurally bounded, so the
  statement evaluator needs fuel whether or not a call is involved.
  Measured: **64 of the 84 contain a call and 20 do not** — and those 20
  need fuel just the same.
* **Inch 5, with CALLS**, through `CallHandler`.

Expressions are fuel-free because neither construct is one.

## The monad, and its layer order

```
EvalM α := ExceptT Refusal (StateT Mem Id) α
```

**State OUTSIDE `Except` — the state-RETAINING order.** The `mvcgen`
pilot proved by `rfl` that `StateT σ (ExceptT ρ …)` discards the state on
a raise, which would make every refusal forget what the program had
already written. `Run.exn` carries a state field for exactly this reason,
and the C scoreboard's REFUSE rows are worth much less if they cannot say
what had happened by the time the refusal fired.

**Every refusal routes through a NAMED primitive** (`refuseUB`,
`refuseValue`, `refuseUnsupported`, `refuseLibc`) rather than a bare
polymorphic `throw`, which the pilot found unusable. That is also the
shape `@[spec]` lemmas want, so the law and the tooling agree.

## The order the census imposed

Inch 2's census measured which operations actually carry the traffic, and
this file is written in that order rather than the standard's:

| | sites | |
| --- | ---: | --- |
| lvalue conversion (§6.3.2.1p2) | **1837** | the load-bearing implicit |
| array-to-pointer decay (§6.3.2.1p3) | **405** | the common path |
| `p->f` (§6.5.3.4) | **226** | …and its partner |
| `&` (§6.5.4.2p3) | 106 | the rare case |
| `*` (§6.5.4.2p4) | 24 | the rarest |

**`evalLValue` has exactly five cases, and the census is why**: the 1837
lvalue conversions take their operand from `DeclRefExpr` 1406,
`MemberExpr` 248, `ArraySubscriptExpr` 169, `UnaryOperator` (`*`) 13, and
`CompoundLiteralExpr` 1 — and the 287 assignments plus 63
increments target the same four kinds. One function serves both.
-/

namespace LeanModels.C.C23

open LeanModels.C (CType Expr CSpan)

/-! ## The evaluation monad -/

/-- The expression evaluator's monad. See the module docstring: `ExceptT`
OUTSIDE `StateT` is the state-retaining order, and it is not the obvious
one. -/
abbrev EvalM (α : Type) := ExceptT Refusal (StateT Mem Halt) α

/-- Run an evaluation against a starting memory, keeping BOTH halves: the
outcome and the memory as it stood when the outcome was produced. A
refusal that threw away its memory could not say what had happened.

The `Halt` wrapper is the uncatchable layer (`Memory.lean` §3.4) — a
`timeout` or an out-of-tier construct answers there and carries no
`Mem` alongside, because neither is an observation. -/
def EvalM.run (m : Mem) (x : EvalM α) : Halt (Except Refusal α × Mem) :=
  StateT.run x m

/-- The run's VERDICT, in `docs/c23-goal.md` §3's vocabulary. This is what
a scoreboard reads, and it is where the diagnostic snapshot stops: there
is nowhere to put a `Mem` in an `Outcome`. -/
def EvalM.verdict (m : Mem) (x : EvalM α) : Outcome α :=
  match EvalM.run m x with
  | .ok (.ok a, _) => .ok a
  | .ok (.error r, _) => .refused r
  | .timeout => .timeout
  | .unsupported w _ => .unsupported w

/-! ### The named refusal primitives

`docs/backlog.md` §L61: *never a bare polymorphic `throw`* — route
refusals through named primitives, each of which can carry its own
`@[spec]`. The three never-pooled causes are one constructor each, so the
partition is structural rather than a convention. -/

/-- Refuse with undefined behavior from the MEMORY rules (§2 of the
memory model). Cause: `ub`, which never retires. -/
def refuseUB (f : MemFault) : EvalM α := throw (.memUB f)

/-- Refuse with undefined behavior from the VALUE rules (§6.5.1p5 and
friends). Cause: `ub`. -/
def refuseValue (u : UB) : EvalM α := throw (.valueUB u)

/-- Refuse a construct outside the tier's vocabulary. Cause:
`unsupported`, which retires by climbing a rung.

**It answers in `Halt`, not in `ExceptT`** — per §3.4, an out-of-tier
refusal is uncatchable by definition rather than by a per-construct
proof. And **this primitive performs the `get` itself**, capturing the
memory as it stood AT the refusal site, so no call site can forget to.
That snapshot is diagnostic only: `Halt`'s `BEq` ignores it and
`Outcome` drops it. -/
def refuseUnsupported (what : String) : EvalM α := fun m =>
  Halt.unsupported what (some m)

/-- Refuse an unmodeled library function. Cause: `libc`, which retires by
widening the slice. -/
def refuseLibc (name : String) : EvalM α := throw (.libc name)

/-! ### Lifting the memory model

Inch 2's operations are pure functions over `Mem`. These are the lifts,
and they are the reason inch 2 threaded `Mem` explicitly: not one of its
definitions had to be rewritten. -/

/-- Read through a pure memory operation. -/
def readMem (f : Mem → MRes α) : EvalM α := do
  match f (← get) with
  | .ok a => pure a
  | .error e => throw e

/-- Write through a pure memory operation. The new memory is committed
only on success; on a refusal the OLD memory is retained, which is the
layer order doing its job. -/
def writeMem (f : Mem → MRes Mem) : EvalM Unit := do
  match f (← get) with
  | .ok m => set m
  | .error e => throw e

/-! ## §6.2.5 — resolving a type spelling to an integer type

**The census found a real problem here.** `CType` is clang's unparsed
`qualType` string (`docs/c-envelope-schema.md` §3), so **type equality is
SPELLING equality** — and the corpus contains 19 binary-operator sites
whose operands have different spellings for the SAME type
(`uint64_t` vs `unsigned long long`, `uint32_t` vs `unsigned int`).
A model that compared type strings would see a conversion that is not
there.

So the evaluator never compares spellings; it RESOLVES them. The table is
the census's own list of the integer spellings that occur, and the widths
come from the profile (`char_bit_8`, `int_32`, `long_64`), not from a
host. -/

/-- Resolve a type spelling to a C integer type.

The standard names come from §6.2.5; the exact-width names are
`<stdint.h>`'s (§7.22), which fixes them exactly, so they resolve under
the profile's widths rather than being guessed. `char`'s signedness is
the profile fact `char_signed`, answering `J.3.5(5)`.

`none` means "not an integer type here" — a struct, a pointer, a float,
`void`, or a spelling outside the census. Every consumer refuses on
`none` rather than inventing a width. -/
def intTyOf? (ty : CType) : Option IntTy :=
  match ty with
  | "char" => some IntTy.char_
  | "signed char" => some IntTy.char_
  | "unsigned char" => some IntTy.uchar
  | "short" | "short int" => some IntTy.short_
  | "unsigned short" | "unsigned short int" => some IntTy.ushort
  | "int" | "signed int" => some IntTy.int_
  | "unsigned" | "unsigned int" => some IntTy.uint
  | "long" | "long int" => some IntTy.long_
  | "unsigned long" | "unsigned long int" => some IntTy.ulong
  | "long long" | "long long int" => some IntTy.long_
  | "unsigned long long" | "unsigned long long int" => some IntTy.ulong
  -- <stdint.h> exact-width names: fixed by the header, resolved by the profile
  | "int8_t" => some IntTy.char_
  | "uint8_t" => some IntTy.uchar
  | "int16_t" => some IntTy.short_
  | "uint16_t" => some IntTy.ushort
  | "int32_t" => some IntTy.int_
  | "uint32_t" => some IntTy.uint
  | "int64_t" => some IntTy.long_
  | "uint64_t" => some IntTy.ulong
  | "_Bool" | "bool" => some IntTy.uchar
  -- QUALIFIED spellings, tabled rather than stripped. Measured: these four
  -- are the ONLY qualified integer spellings on an expression node in the
  -- corpus (`const int` 35, `const char` 30, `const unsigned char` 18,
  -- `const uint64_t` 4) — zero `volatile`, zero `restrict`, zero `_Atomic`.
  -- A table fails loudly on an unmeasured spelling where string surgery
  -- would quietly accept one.
  | "const char" => some IntTy.char_
  | "const unsigned char" => some IntTy.uchar
  | "const int" => some IntTy.int_
  | "const unsigned int" => some IntTy.uint
  | "const long" => some IntTy.long_
  | "const unsigned long" => some IntTy.ulong
  | "const uint64_t" => some IntTy.ulong
  | "const uint32_t" => some IntTy.uint
  | _ => none

/-- The integer type of an expression, or a refusal naming the spelling.
A refusal a human cannot act on is a refusal that has not done its job,
so the unresolved SPELLING is carried in the message. -/
def intTyOf (ty : CType) : EvalM IntTy :=
  match intTyOf? ty with
  | some t => pure t
  | none => refuseUnsupported s!"not an integer type: '{ty}'"

/-! ## The environment

An expression cannot change which names are in scope — only a declaration
can, and declarations are inch 4 — so the environment is a read-only
PARAMETER here rather than part of the state. Measured: 250 block-scope
objects, of which **zero** are `static`, so a name maps to one object for
the lifetime of its frame. -/

/-- Names in scope, innermost first. -/
abbrev Env := List (String × ObjId)

/-- Resolve a name to its object. Innermost binding wins (§6.2.1). -/
def Env.lookup? (env : Env) (name : String) : Option ObjId :=
  (env.find? (·.1 == name)).map (·.2)

/-! ## Calls — the handler, and where fuel will arrive

Inch 3 is fuel-free (module docstring). A call is the one expression that
can recurse into an arbitrary function body, so it is not evaluated here:
it is delegated to a HANDLER supplied by the caller. Inch 5 supplies one
that threads fuel; until then `noCalls` refuses, loudly and by cause. -/

/-- Peel the conversions clang wraps a callee in and read its name.
`"<indirect>"` is a call through a pointer — measured 19, every one
through the `movecb` callback parameter. -/
def calleeNameOf : Expr → String
  | .implicitCast _ s _ _ => calleeNameOf s
  | .paren s _ _ => calleeNameOf s
  | .declRef n _ _ _ => n
  | _ => "<indirect>"

/-- What a call site delegates to: the callee and the ARGUMENT
EXPRESSIONS, **unevaluated**.

Taking expressions rather than values is what keeps this layer fuel-free.
Evaluating the arguments is the handler's job, and inch 5's handler will
do it with fuel in hand — so the recursion that needs fuel lives where
fuel lives, and `evalExpr` never recurses through a `List Expr`. -/
abbrev CallHandler := Expr → List Expr → EvalM CVal

/-- The inch-3 handler: every call refuses as `unsupported`, which is the
cause that retires by climbing a rung — NOT `libc`, and never silently. -/
def noCalls : CallHandler := fun callee _ =>
  refuseUnsupported s!"call to '{calleeNameOf callee}' — the call semantics is inch 5"

/-! ## Layout — the implementation-defined surface, PARAMETERIZED

`sizeof` and `offsetof` are **implementation-defined** (`J.3.10`), so
they are not baked in: they arrive the way the integer widths do, as
facts a profile supplies and a probe can check on any host. The fixture
instantiates this with offsets measured by `_Static_assert` on BOTH hosts
in `docs/c-profile.json`, which agree.

Deriving layout from the type spellings inside Lean would mean writing
the C type parser `docs/c-envelope-schema.md` §3 exists to avoid. -/

/-- The implementation-defined layout facts an evaluator needs.

Every table is keyed on the type spelling **exactly as the AST carries
it** — `"Pos"`, `"const Pos *"` — never on a parsed type. That is the
same decision `docs/c-envelope-schema.md` §3 made for `CType` itself, and
it is what keeps the C type parser out of the tier. -/
structure Layout where
  /-- `sizeof(ty)` in bytes (§6.5.4.4). -/
  size : CType → Option Nat
  /-- `offsetof`, keyed on the BASE expression's spelling, so `p->f` and
  `x.f` look up under `"const Pos *"` and `"Pos"` respectively. -/
  fieldOff : CType → String → Option Nat

/-- A layout that knows nothing: every query refuses. The DEFAULT, so a
missing layout fact is a loud refusal rather than a guessed offset. -/
def Layout.unknown : Layout := ⟨fun _ => none, fun _ _ => none⟩

/-! ## The evaluation context

Read-only for the whole of an expression: an expression cannot change
which names are in scope, what a struct's layout is, or what a call
means. Bundled so the five mutually recursive functions below take one
parameter instead of four. -/

/-- Everything an expression evaluation reads but never writes. -/
structure Ctx where
  env : Env
  /-- Enumeration constants, folded to integers by the ingester
  (`docs/c-envelope-schema.md` §3.1). Measured: 11 in the corpus. -/
  enums : List (String × Int) := []
  layout : Layout := Layout.unknown
  call : CallHandler := noCalls

/-! ## §6.5.14p3 — scalar truth

`&&`, `||`, `!` and every controlling expression ask one question:
does this value compare unequal to 0? A pointer answers it too
(§6.5.10p3: a null pointer constant compares equal to a null pointer),
and `undef` REFUSES rather than guessing. -/

/-- Does this value compare unequal to zero? -/
def truthy (v : CVal) : EvalM Bool :=
  match v with
  | .int _ n => pure (n != 0)
  | .ptr p => pure (!p.isNull)
  | .undef => refuseUB (.indetAutomatic 0 0)

/-- §6.5.9p3 / §6.5.10p3: a comparison yields `int`, 0 or 1. -/
def ofBool (b : Bool) : CVal := .int IntTy.int_ (if b then 1 else 0)

/-! ## §6.5.6-§6.5.13 — the binary arithmetic rules

The operands arrive ALREADY CONVERTED. Measured: of 563 arithmetic and
comparison sites, **542 have operand types that resolve equal** and the
21 that differ are 19 typedef-spelling aliases plus 2 pointer arithmetic
— so clang's implicit `IntegralCast` nodes have already performed
§6.3.1.8's usual arithmetic conversions and the tier reads a promotion
off rather than re-deriving one.

Shifts are counted apart on purpose: §6.5.8p3 promotes each operand
SEPARATELY and the result type is the left operand's, so a shift's
operands legitimately differ (measured: 17 sites, all `uint64_t << int`
or `int << int`). -/

/-- Apply an integer binary operator, at the type the frontend assigned.
Every arm is `Value.lean`'s, so the wrap/refuse split and its J.2 indices
are inherited rather than restated. -/
def intBinop (op : String) (t : IntTy) (a b : Int) : EvalM CVal :=
  let lift (r : CRes CVal) : EvalM CVal :=
    match r with
    | .ok v => pure v
    | .ub u => refuseValue u
  match op with
  | "+" => lift (addOp t a b)
  | "-" => lift (subOp t a b)
  | "*" => lift (mulOp t a b)
  | "/" => lift (divOp t a b)
  | "%" => lift (modOp t a b)
  | "<<" => lift (shlOp t a b)
  | ">>" => lift (shrOp t a b)
  -- §6.5.11-§6.5.13: bitwise AND/XOR/OR. Both operands are already at `t`,
  -- and the result is in range by construction, so no arm can overflow.
  | "&" => pure (.int t (bitAnd t a b))
  | "|" => pure (.int t (bitOr t a b))
  | "^" => pure (.int t (bitXor t a b))
  -- §6.5.9p3 / §6.5.10p3: relational and equality yield `int`.
  | "<" => pure (ofBool (a < b))
  | ">" => pure (ofBool (a > b))
  | "<=" => pure (ofBool (a ≤ b))
  | ">=" => pure (ofBool (a ≥ b))
  | "==" => pure (ofBool (a == b))
  | "!=" => pure (ofBool (a != b))
  | _ => refuseUnsupported s!"binary operator '{op}'"

/-! ### Projecting a value

Named, because every refusal must be. -/

/-- Require a pointer. `undef` and an integer both refuse. -/
def asPtr (v : CVal) : EvalM Ptr :=
  match v with
  | .ptr p => pure p
  | .int _ _ => refuseUnsupported "integer used as a pointer (no int↔ptr cast in tier)"
  | .undef => refuseUB (.indetAutomatic 0 0)

/-- Require an integer, with its type. -/
def asInt (v : CVal) : EvalM (IntTy × Int) :=
  match v with
  | .int t n => pure (t, n)
  | .ptr _ => refuseUnsupported "pointer used as an integer (no ptr↔int cast in tier)"
  | .undef => refuseUB (.indetAutomatic 0 0)

/-- Is this spelling a pointer type? Spelling-based, and deliberately so:
the tier carries clang's `qualType` string rather than a type tree
(`docs/c-envelope-schema.md` §3). Measured: 199 distinct pointer/array
spellings on expression nodes, every one ending in `*` or `]`. -/
def isPtrType (ty : CType) : Bool := ty.endsWith "*"

/-- Load whatever an lvalue of this type holds — an integer or a pointer.
§6.3.2.1p2, the lvalue conversion: **1837 sites, the load-bearing
implicit of the whole corpus.** -/
def loadAt (p : Ptr) (ty : CType) : EvalM CVal :=
  if isPtrType ty then do
    let q ← readMem (fun m => Mem.loadPtr m p)
    pure (.ptr q)
  else do
    let t ← intTyOf ty
    readMem (fun m => Mem.loadInt m p t)

/-- Store a value at an address, at the lvalue's type. -/
def storeAt (p : Ptr) (ty : CType) (v : CVal) : EvalM Unit :=
  match v with
  | .ptr q => writeMem (fun m => Mem.storePtr m p q)
  | .int _ n => do
      let t ← intTyOf ty
      writeMem (fun m => Mem.storeInt m p t n)
  | .undef => refuseUnsupported "storing an indeterminate value"

/-- Peel the conversions clang wraps a callee in and read its name.
`none` is an INDIRECT call — measured 19, every one through `movecb`. -/
def calleeName : Expr → Option String
  | .implicitCast _ s _ _ => calleeName s
  | .paren s _ _ => calleeName s
  | .declRef n "FunctionDecl" _ _ => some n
  | _ => none

/-! ## §6.5 — the evaluator

Two mutually recursive functions and one list helper, all STRUCTURALLY
recursive on `Expr` (module docstring: this layer is fuel-free).

`evalLValue` yields the ADDRESS an expression designates; `evalExpr`
yields its VALUE. The census says the first has exactly five shapes. -/

/-- The arithmetic operator inside a compound assignment.

TABLED, not derived by dropping the `=`: the census says the corpus uses
exactly five (`+=` 10, `|=` 6, `^=` 3, `-=` 3, `*=` 2), and a table
refuses an unmeasured spelling where string surgery would quietly accept
one. The empty string is not an operator, so an unlisted spelling reaches
`evalArith`'s own refusal. -/
def compoundBase : String → String
  | "+=" => "+" | "-=" => "-" | "*=" => "*" | "/=" => "/" | "%=" => "%"
  | "&=" => "&" | "|=" => "|" | "^=" => "^"
  | "<<=" => "<<" | ">>=" => ">>"
  | _ => ""

/-- The non-short-circuit binary rules, once both operands have values. -/
def evalArith (ctx : Ctx) (op : String) (lv rv : CVal) (ty : CType) : EvalM CVal :=
  match lv, rv with
  -- §6.5.7p8 — pointer + integer, and it is the pointer rule that applies
  -- whenever either operand is one. Measured: 8 `+`, 4 `-`.
  | .ptr p, .int _ i =>
      if op == "+" || op == "-" then
        match ctx.layout.size ty with
        | some esz => do
            let d := if op == "+" then i else -i
            let q ← readMem (fun m => Mem.offsetPtr m p esz d)
            pure (.ptr q)
        | none => refuseUnsupported s!"no size for pointee of '{ty}'"
      else refuseUnsupported s!"operator '{op}' on a pointer and an integer"
  | .int _ i, .ptr p =>
      if op == "+" then
        match ctx.layout.size ty with
        | some esz => do
            let q ← readMem (fun m => Mem.offsetPtr m p esz i)
            pure (.ptr q)
        | none => refuseUnsupported s!"no size for pointee of '{ty}'"
      else refuseUnsupported s!"operator '{op}' on an integer and a pointer"
  -- §6.5.10p7 vs §6.5.9p6 — the asymmetry: `==`/`!=` across unrelated
  -- objects is DEFINED, `<` and friends are UNDEFINED.
  | .ptr a, .ptr b =>
      if op == "==" then pure (ofBool (Mem.ptrEq a b))
      else if op == "!=" then pure (ofBool (!Mem.ptrEq a b))
      else if op == "<" then do let c ← readMem (fun _ => Mem.ptrLt a b); pure (ofBool c)
      else if op == ">" then do let c ← readMem (fun _ => Mem.ptrLt b a); pure (ofBool c)
      else if op == "<=" then do let c ← readMem (fun _ => Mem.ptrLt b a); pure (ofBool (!c))
      else if op == ">=" then do let c ← readMem (fun _ => Mem.ptrLt a b); pure (ofBool (!c))
      else refuseUnsupported s!"operator '{op}' on two pointers"
  | .int t a, .int _ b =>
      -- Shifts take the LEFT operand's type (§6.5.8p3); every other
      -- operator has already had both operands converted to a common type.
      if op == "<<" || op == ">>" then intBinop op t a b
      else match intTyOf? ty with
        | some rt => intBinop op rt a b
        | none => intBinop op t a b        -- a comparison: the result is `int`
  | _, _ => refuseUB (.indetAutomatic 0 0)

/-! ## §6.5 — the evaluator

Two mutually recursive functions, both STRUCTURALLY recursive on `Expr`
(module docstring: this layer is fuel-free). `evalLValue` yields the
ADDRESS an expression designates; `evalExpr` yields its VALUE.

Written in the CENSUS's order, not the standard's: the conversion lattice
first (1837 + 405 sites), then the short-circuits whose rule is not
"evaluate both", then everything else. -/

mutual

/-- §6.3.2.1p1 — an expression in LVALUE position, yielding the address
it designates.

**Five cases, and the census chose them**: the 1837 lvalue conversions
take their operand from `DeclRefExpr` 1406, `MemberExpr` 248,
`ArraySubscriptExpr` 169, `UnaryOperator` (`*`) 13 and
`CompoundLiteralExpr` 1; the 287 assignments and 63 increments target the
same kinds. Anything else in lvalue position is a refusal, never a
fallthrough. -/
def evalLValue (ctx : Ctx) : Expr → EvalM Ptr
  | .paren sub _ _ => evalLValue ctx sub
  -- §6.5.2p2: an identifier designating an object is an lvalue.
  | .declRef name _ _ _ =>
      match ctx.env.lookup? name with
      | some o => pure (Ptr.toObject o)
      | none => refuseUnsupported s!"unbound name '{name}'"
  -- §6.5.3.4p4: `p->f` is DEFINED as `(*p).f`, so the two spellings are
  -- ONE rule here. 226 arrow sites, 184 dot.
  | .member base field arrow _ _ => do
      let basePtr ← if arrow then (do let v ← evalExpr ctx base; asPtr v)
                    else evalLValue ctx base
      match ctx.layout.fieldOff base.ty field with
      | some off => pure (Mem.member basePtr off)
      | none => refuseUnsupported s!"no layout for field '{field}'"
  -- §6.5.3.2p2: `a[i]` is DEFINED as `*(a + i)`. The base arrives already
  -- decayed (clang inserts ArrayToPointerDecay), so it is a VALUE here.
  | .index base idx ty _ => do
      let bv ← evalExpr ctx base
      let bp ← asPtr bv
      let iv ← evalExpr ctx idx
      let (_, i) ← asInt iv
      match ctx.layout.size ty with
      | some esz => readMem (fun m => Mem.subscript m bp esz i)
      | none => refuseUnsupported s!"no size for element type '{ty}'"
  -- §6.5.4.2p4: the operand of unary `*` is a pointer VALUE.
  | .unop op sub _ _ _ =>
      if op == "*" then (do let v ← evalExpr ctx sub; asPtr v)
      else refuseUnsupported s!"unary '{op}' is not an lvalue"
  | .compoundLit .. => refuseUnsupported "compound literal (inch 4: it needs an object)"
  | e => refuseUnsupported s!"not an lvalue: {e.kindName}"

/-- §6.5 — an expression in VALUE position. -/
def evalExpr (ctx : Ctx) : Expr → EvalM CVal
  | .paren sub _ _ => evalExpr ctx sub

  -- ===== §6.3 — the conversion lattice, all eight castKinds =====
  | .implicitCast ck sub ty _
  | .cast ck sub ty _ =>
      if ck == "LValueToRValue" then do
        -- §6.3.2.1p2 — 1837 sites, the load-bearing implicit of the corpus.
        let p ← evalLValue ctx sub
        loadAt p ty
      else if ck == "ArrayToPointerDecay" then do
        -- §6.3.2.1p3 — 405 sites, the LARGEST pointer producer there is.
        let p ← evalLValue ctx sub
        pure (.ptr p)
      else if ck == "NullToPointer" then
        -- §6.3.2.3p3 — a null pointer constant becomes a null pointer.
        pure (.ptr Ptr.null)
      else if ck == "IntegralCast" then do
        -- §6.3.1.3 — defined to unsigned; to signed it is the PROFILE's
        -- answer to `J.3.6(3)`, not the standard's (see `Value.convert`).
        let v ← evalExpr ctx sub
        let (_, n) ← asInt v
        let t ← intTyOf ty
        pure (convert t n)
      else if ck == "NoOp" then
        -- A qualifier or typedef change: the VALUE is untouched. 217 sites,
        -- and they are why type equality must be resolution, not spelling.
        evalExpr ctx sub
      else if ck == "BitCast" then
        -- §6.3.2.3p1 — `void*` ↔ `T*`. Provenance carried, not recomputed:
        -- 52 sites, all void-pointer conversions, ZERO type punning.
        evalExpr ctx sub
      else if ck == "FunctionToPointerDecay" then
        refuseUnsupported "function-to-pointer decay (inch 5)"
      else if ck == "IntegralToFloating" then
        refuseUnsupported "integer-to-floating conversion (floats: a named decision)"
      else refuseUnsupported s!"castKind '{ck}'"

  -- ===== §6.5.14 / §6.5.15 — THE DRAIN AMENDMENT =====
  -- A short-circuiting construct's out-memory is a function of its ANSWER.
  -- The unevaluated operand is never run, so the memory it WOULD have
  -- produced never exists — there is nothing to speak about, which is
  -- precisely what the amendment forbids concluding. 181 sites in all.
  | .binop op l r ty _ =>
      if op == "&&" then do
        -- §6.5.14p4: the right operand is evaluated ONLY if the left
        -- compares unequal to 0 — and §6.5.14p4 also makes this a SEQUENCE
        -- POINT, which is what makes a two-step threading expressible.
        let lv ← evalExpr ctx l
        let lb ← truthy lv
        if !lb then pure (ofBool false)
        else do let rv ← evalExpr ctx r; let rb ← truthy rv; pure (ofBool rb)
      else if op == "||" then do
        -- §6.5.15p4: …only if the left compares EQUAL to 0.
        let lv ← evalExpr ctx l
        let lb ← truthy lv
        if lb then pure (ofBool true)
        else do let rv ← evalExpr ctx r; let rb ← truthy rv; pure (ofBool rb)
      else if op == "," then do
        -- §6.5.18p2: both, in order, the left value discarded. 1 site.
        let _ ← evalExpr ctx l
        evalExpr ctx r
      else if op == "=" then do
        -- §6.5.17.2 — simple assignment, 287 sites. The store is sequenced
        -- after the right operand's value computation, which is why the
        -- sequencing census could admit 53 of its 73 multi-effect full
        -- expressions by inspection (`docs/c-semantics-design.md` §4.4).
        let p ← evalLValue ctx l
        let v ← evalExpr ctx r
        storeAt p l.ty v
        pure v
      else do
        let lv ← evalExpr ctx l
        let rv ← evalExpr ctx r
        evalArith ctx op lv rv ty

  -- §6.5.16p4 — `?:`, the third short-circuit: EXACTLY ONE arm runs. 42 sites.
  | .cond c t e _ _ => do
      let cv ← evalExpr ctx c
      let b ← truthy cv
      if b then evalExpr ctx t else evalExpr ctx e

  -- ===== §6.5.3.5 / §6.5.4 — unary =====
  | .unop op sub post ty _ =>
      if op == "&" then do
        -- §6.5.4.2p3 — address-of, 106 sites. It does NOT read the object.
        let p ← evalLValue ctx sub
        pure (.ptr p)
      else if op == "*" then do
        -- §6.5.4.2p4 — indirection reaching value position directly.
        let v ← evalExpr ctx sub
        let p ← asPtr v
        loadAt p ty
      else if op == "!" then do
        -- §6.5.4.3p5 — `!x` is `(0 == x)`. 80 sites.
        let v ← evalExpr ctx sub
        let b ← truthy v
        pure (ofBool (!b))
      else if op == "-" then do
        -- §6.5.4.3p3 — unary minus OVERFLOWS at `-INT_MIN`: `J.2(35)`.
        let v ← evalExpr ctx sub
        let (t, n) ← asInt v
        match negOp t n with
        | .ok r => pure r
        | .ub u => refuseValue u
      else if op == "+" then evalExpr ctx sub
      else if op == "++" || op == "--" then do
        -- §6.5.3.5 — and MEASURED: all 63 increment sites in the corpus are
        -- POSTFIX; it never writes `++i`. Postfix yields the value BEFORE
        -- the update, and the update itself can overflow (`J.2(35)`).
        let p ← evalLValue ctx sub
        let old ← loadAt p sub.ty
        let (t, n) ← asInt old
        match (if op == "++" then addOp t n 1 else subOp t n 1) with
        | .ub u => refuseValue u
        | .ok nv => do
            storeAt p sub.ty nv
            pure (if post then old else nv)
      else refuseUnsupported s!"unary operator '{op}'"

  -- §6.5.17.3 — compound assignment: `a op= b` is `a = a op b` with the
  -- lvalue evaluated ONCE. 24 sites (`+=` 10, `|=` 6, `^=` 3, `-=` 3, `*=` 2).
  | .compoundAssign op l r ty _ => do
      let p ← evalLValue ctx l
      let old ← loadAt p l.ty
      let rv ← evalExpr ctx r
      let nv ← evalArith ctx (compoundBase op) old rv ty
      storeAt p l.ty nv
      pure nv

  -- ===== lvalues reaching value position without a conversion =====
  -- Clang wraps scalar reads in `LValueToRValue`, so these are the
  -- aggregate-valued cases; evaluating the address and loading is the rule
  -- either way (§6.3.2.1p2).
  | .member base field arrow ty sp => do
      let p ← evalLValue ctx (.member base field arrow ty sp)
      loadAt p ty
  | .index base idx ty sp => do
      let p ← evalLValue ctx (.index base idx ty sp)
      loadAt p ty

  -- ===== §6.4.4 — constants =====
  | .intLit v ty _ => do
      let t ← intTyOf ty
      match v.toInt? with
      | some n => pure (.int t n)
      | none => refuseUnsupported s!"integer literal spelling '{v}'"
  | .charLit v ty _ => do
      let t ← intTyOf ty
      match v.toInt? with
      | some n => pure (.int t n)
      | none => refuseUnsupported s!"character literal spelling '{v}'"
  | .strLit .. => refuseUnsupported "string literal (inch 4: it needs a static object)"
  | .floatLit .. => refuseUnsupported "floating literal (floats are a named decision)"

  -- A bare name in value position is an enumeration constant; every other
  -- name arrives wrapped in a conversion or a decay.
  | .declRef name declKind ty _ =>
      if declKind == "EnumConstantDecl" then
        match (ctx.enums.find? (·.1 == name)).map (·.2) with
        | some n => do let t ← intTyOf ty; pure (.int t n)
        | none => refuseUnsupported s!"unknown enum constant '{name}'"
      else refuseUnsupported s!"name '{name}' in value position without a conversion"

  -- §6.5.3.3 — the call, DELEGATED. This layer is fuel-free precisely
  -- because it does not evaluate the arguments; see `CallHandler`.
  | .call callee args _ _ => ctx.call callee args

  -- §6.5.4.4 — `sizeof`, answered by the layout, never computed here.
  | .typeTrait trait argTy sub ty _ =>
      if trait != "sizeof" then refuseUnsupported s!"type trait '{trait}'"
      else
        let key := match argTy with
                   | some a => some a
                   | none => sub.map Expr.ty
        match key.bind ctx.layout.size with
        | some n => do let t ← intTyOf ty; pure (.int t (n : Int))
        | none => refuseUnsupported "sizeof: no layout for the operand type"

  | .constExpr v _ ty _ => do
      let t ← intTyOf ty
      match v.toInt? with
      | some n => pure (.int t n)
      | none => refuseUnsupported s!"constant expression '{v}'"
  | .initList .. => refuseUnsupported "initializer list (inch 4)"
  | .compoundLit .. => refuseUnsupported "compound literal (inch 4)"
  | .unsupported k _ _ => refuseUnsupported s!"out of tier: {k}"

end

/-! ## Spec lemmas — arm level, and the drain amendment

`docs/backlog.md` §L61 measured what altitude buys here: unfolded
primitives produced **259 verification conditions and FAILED**, four
triples produced **12 and closed**. So the primitives get lemmas at ARM
granularity — one per branch, not one per function — because a branch is
what a proof actually lands on.

These are stated as plain rewrite lemmas rather than `Std.Do` `@[spec]`
triples. The SHAPE is the same (a pre-condition on the arm, a determined
post), which is what `docs/c-semantics-design.md` §4.1a asks for; wiring
them to `mvcgen` is inch 4's, once `CWorld` fixes the state type. -/

section Spec

variable {α : Type}

/-- `truthy`'s nonzero arm. -/
@[simp] theorem truthy_int_ne (t : IntTy) (n : Int) (h : n ≠ 0) :
    truthy (.int t n) = pure true := by
  have hb : (n != 0) = true := by simp [h]
  simp [truthy, hb]

/-- `truthy`'s zero arm — the one the short circuit turns on. -/
@[simp] theorem truthy_int_zero (t : IntTy) : truthy (.int t 0) = pure false := by
  simp [truthy]

/-- `truthy`'s null-pointer arm (§6.5.10p3). -/
@[simp] theorem truthy_ptr_null : truthy (.ptr Ptr.null) = pure false := by
  simp [truthy, Ptr.isNull, Ptr.null]

/-- `asInt`'s success arm. -/
@[simp] theorem asInt_int (t : IntTy) (n : Int) : asInt (.int t n) = pure (t, n) := by
  simp [asInt]

/-- `asPtr`'s success arm. -/
@[simp] theorem asPtr_ptr (p : Ptr) : asPtr (.ptr p) = pure p := by
  simp [asPtr]

/-- Running a `pure` keeps the memory it was handed. -/
@[simp] theorem run_pure (m : Mem) (a : α) :
    EvalM.run m (pure a : EvalM α) = .ok (.ok a, m) := rfl

end Spec

/-! ### §6.5.14p4 — the drain amendment, as a theorem

> **A short-circuiting construct's out-world is a function of its ANSWER;
> the world goes in the HYPOTHESIS, never the conclusion.**

Read the statement below for what it does NOT say. `r` — the right
operand — appears only as an argument to the constructor. It appears in
no hypothesis and in no part of the conclusion. The out-memory named in
the conclusion is `m'`, which the HYPOTHESIS introduced as the LEFT
operand's out-memory.

That is the amendment: when the left operand answers 0, the memory the
right operand would have produced never exists, so the theorem cannot and
does not mention it. A statement of the form "…the out-world is the
right's…" would be unprovable here, which is the point. -/

/-- §6.5.14p4 — `&&` short-circuits: a false left operand answers 0 **in
the left operand's own out-memory**, whatever the right operand is. -/
theorem and_shortCircuits (ctx : Ctx) (l r : Expr) (ty : CType) (sp : CSpan)
    (m m' : Mem) (t : IntTy)
    (hl : EvalM.run m (evalExpr ctx l) = .ok (.ok (.int t 0), m')) :
    EvalM.run m (evalExpr ctx (.binop "&&" l r ty sp)) = .ok (.ok (ofBool false), m') := by
  simp only [EvalM.run, StateT.run] at hl ⊢
  simp [evalExpr, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, bind, StateT.bind,
    hl, truthy, ofBool, pure, ExceptT.pure, StateT.pure]

/-- §6.5.15p4 — `||` is the mirror: a TRUE left operand answers 1 in the
left operand's own out-memory, and the right operand is not evaluated. -/
theorem or_shortCircuits (ctx : Ctx) (l r : Expr) (ty : CType) (sp : CSpan)
    (m m' : Mem) (t : IntTy) (n : Int) (hn : n ≠ 0)
    (hl : EvalM.run m (evalExpr ctx l) = .ok (.ok (.int t n), m')) :
    EvalM.run m (evalExpr ctx (.binop "||" l r ty sp)) = .ok (.ok (ofBool true), m') := by
  simp only [EvalM.run, StateT.run] at hl ⊢
  simp [evalExpr, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, bind, StateT.bind,
    hl, hn, truthy, ofBool, pure, ExceptT.pure, StateT.pure]

/-- §6.5.16p4 — `?:` evaluates EXACTLY ONE arm, and the theorem names
only the arm that ran. -/
theorem cond_takesOneArm (ctx : Ctx) (c t e : Expr) (ty : CType) (sp : CSpan)
    (m m' : Mem) (it : IntTy)
    (hc : EvalM.run m (evalExpr ctx c) = .ok (.ok (.int it 0), m')) :
    EvalM.run m (evalExpr ctx (.cond c t e ty sp)) = EvalM.run m' (evalExpr ctx e) := by
  simp only [EvalM.run, StateT.run] at hc ⊢
  simp [evalExpr, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, bind, StateT.bind,
    hc, truthy, pure, ExceptT.pure, StateT.pure]

#print axioms and_shortCircuits
#print axioms or_shortCircuits
#print axioms cond_takesOneArm

end LeanModels.C.C23
