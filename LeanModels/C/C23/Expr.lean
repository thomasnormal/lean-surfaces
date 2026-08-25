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
abbrev EvalM (α : Type) := SemMWith Mem Refusal CDetail Mem α

/-- Run an evaluation against a starting memory, keeping BOTH halves: the
outcome and the memory as it stood when the outcome was produced. A
refusal that threw away its memory could not say what had happened.

The `Halt` wrapper is the uncatchable layer (`Memory.lean` §3.4) — a
`timeout` or an out-of-tier construct answers there and carries no
`Mem` alongside, because neither is an observation. -/
def EvalM.run (m : Mem) (x : EvalM α) :
    Except (Loud CDetail Mem) (Except Refusal α × Mem) :=
  StateT.run x m

/-- The run's VERDICT, in `docs/c23-goal.md` §3's vocabulary. This is what
a scoreboard reads, and it is where the diagnostic snapshot stops: there
is nowhere to put a `Mem` in an `Outcome`. -/
def EvalM.verdict (m : Mem) (x : EvalM α) : Outcome α :=
  match EvalM.run m x with
  | .ok (.ok a, _) => .ok a
  | .ok (.error r, _) => .refused r
  | .error .timeout => .timeout
  | .error (.unsupported _ msg _) => .unsupported msg

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

**It answers in the `Halt` BASE, not in `ExceptT`** — per §3.4, an
out-of-tier refusal is uncatchable by definition rather than by a
per-construct proof. And **this primitive takes the memory as its
argument**, capturing it AS IT STOOD at the refusal site, so no call site
can forget to.

The snapshot is diagnostic only, and since the Core adoption **both
guards are enforced in `Core` rather than here**: `Loud`'s `BEq` ignores
the snapshot and `Loud.observable` has nowhere to put one. This tier's
`Outcome` is the third. -/
def refuseUnsupported (what : String) : EvalM α := fun m =>
  .error (.unsupported (.unsupported ()) what (some m))

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

/-- What a call site delegates to: the callee expression and its arguments
**already evaluated, in the CALLER's scope**.

**This signature is the repair of inch 5's open problem, and the two
rejected shapes are worth keeping.** §6.5.3.3p4 evaluates arguments in the
caller's scope, so inch 5 first tried `(Expr → EvalM CVal) → …`, handing
`evalExpr ctx` to the handler as a closure. That broke termination: a
recursive function passed into an OPAQUE callee cannot be shown to
terminate, because nothing constrains what the callee does with it. The
retreat was `List Expr` — unevaluated — which terminated by handing the
handler a job it had no way to do, and every nested call to a defined
function refused.

The shape that works is the one `CallHandler`'s own note predicted:
**`evalArgs` inside the mutual block below, feeding the handler VALUES.**
The recursion is then `evalExpr`'s, where the measure already lives, and
the callee is opaque again because it receives data rather than a function.

**The ORDER is now this layer's, not the handler's**, and that is a
deliberate move of the obligation. §6.5.3.3p10 leaves argument evaluation
indeterminately sequenced (`J.1(16)`); `evalArgs` fixes left-to-right as
the CANONICAL order for extracting witnesses, and Thomas's `∀ order`
ruling becomes a theorem about `evalArgs` — a thing that can be stated —
rather than a property of an opaque handler, which could not be. -/
abbrev CallHandler := Expr → List CVal → EvalM CVal

/-- The handler for a context with **no program behind it**: a bare `Ctx`
knows names, enums and layout, and nothing about function definitions, so
there is nothing to call INTO.

It refuses as `unsupported` — the cause that retires by climbing a rung —
NOT `libc`, and never silently. The arguments have already been evaluated
by then (`evalArgs`), which is deliberate: their effects are the caller's,
and a refusal must not un-happen them.

The message used to read *"the call semantics is inch 5"*. Inch 5 has
landed and `callFn` supplies a real handler; what remains true is only
that THIS context has no program. -/
def noCalls : CallHandler := fun callee _ =>
  refuseUnsupported
    s!"call to '{calleeNameOf callee}' in a context with no program — call it through 'callByName'"

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
  /-- An array type's element type and extent, for `T[N]`.

  Needed because **aggregate initialization WRITES through the layout**
  where reading only ever asked it for one offset: §6.7.11 has to know how
  many elements there are to know which are unmentioned. `none` for a
  non-array type. -/
  elem : CType → Option (CType × Nat) := fun _ => none
  /-- A structure's members, IN DECLARATION ORDER with their types.
  §6.7.11p9 initializes members in order, so the order is load-bearing and
  not a convenience. `none` for a non-structure type. -/
  members : CType → Option (List (String × CType)) := fun _ => none

/-- A layout that knows nothing: every query refuses. The DEFAULT, so a
missing layout fact is a loud refusal rather than a guessed offset. -/
def Layout.unknown : Layout :=
  ⟨fun _ => none, fun _ _ => none, fun _ => none, fun _ => none⟩

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

/-- The POINTEE spelling of a pointer type: `int *` → `int`, `const S *` →
`const S`. `none` when the spelling is not a pointer at all.

This exists because `layout.size` is asked for two DIFFERENT types by two
neighbouring callers, and the difference is invisible at the call site.
At a subscript, clang types `a[i]` as the ELEMENT, so `layout.size ty` is
the stride. At `p + n`, clang types the expression as the POINTER, so the
same phrase asks for the size of a pointer — 8, on every pointee — and
§6.5.7p8's scaling silently became "advance eight bytes". An `int *` walked
in strides of 8 and a 12-byte struct pointer in strides of 8; `a[i]` was
right the whole time, which is why the corpus never showed it. The peel is
one level only: `int **` → `int *`, which is the pointee and is itself a
pointer, exactly as §6.2.5p20 has it. -/
def pointeeOf (ty : CType) : Option CType :=
  if ty.endsWith "*" then some (ty.dropEnd 1).toString.trimAsciiEnd.toString
  else none

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
        match (pointeeOf ty).bind ctx.layout.size with
        | some esz => do
            let d := if op == "+" then i else -i
            let q ← readMem (fun m => Mem.offsetPtr m p esz d)
            pure (.ptr q)
        | none => refuseUnsupported s!"no size for pointee of '{ty}'"
      else refuseUnsupported s!"operator '{op}' on a pointer and an integer"
  | .int _ i, .ptr p =>
      if op == "+" then
        match (pointeeOf ty).bind ctx.layout.size with
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
  | .member base field arrow _ _ => memberAddr ctx base field arrow
  -- §6.5.3.2p2: `a[i]` is DEFINED as `*(a + i)`. The base arrives already
  -- decayed (clang inserts ArrayToPointerDecay), so it is a VALUE here.
  | .index base idx ty _ => indexAddr ctx base idx ty
  -- §6.5.4.2p4: the operand of unary `*` is a pointer VALUE.
  | .unop op sub _ _ _ =>
      if op == "*" then (do let v ← evalExpr ctx sub; asPtr v)
      else refuseUnsupported s!"unary '{op}' is not an lvalue"
  | .compoundLit .. => refuseUnsupported "compound literal (inch 4: it needs an object)"
  | e => refuseUnsupported s!"not an lvalue: {e.kindName}"
  termination_by e => 2 * e.size + 1
  decreasing_by all_goals (simp_wf <;> omega)

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
  | .member base field arrow ty _ => do
      let p ← memberAddr ctx base field arrow
      loadAt p ty
  | .index base idx ty _ => do
      let p ← indexAddr ctx base idx ty
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

  -- §6.5.3.3p4 — the arguments are evaluated HERE, in the caller's scope,
  -- and the handler receives VALUES. Still fuel-free: `evalArgs` is in this
  -- mutual block and shrinks the same `Expr` measure.
  | .call callee args _ _ => do
      let vs ← evalArgs ctx args
      ctx.call callee vs

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
  termination_by e => 2 * e.size + 1
  decreasing_by all_goals (simp_wf <;> omega)

/-- §6.5.3.3p4 — a call's arguments, evaluated in the CALLER's scope,
**left to right**.

This is the function inch 5 named and could not write, and it is in the
mutual block for the reason the failure taught: the recursion it needs is
`evalExpr`'s, so it must sit where `evalExpr`'s measure does. Handing the
evaluator OUT to a handler put the recursion somewhere nothing could
constrain it; keeping it here costs one extra decrease goal.

**LEFT-TO-RIGHT IS THE CANONICAL ORDER, NOT THE CLAIM.** §6.5.3.3p10
leaves argument evaluation *indeterminately sequenced* — `J.1(16)`, the
one Annex J entry this tier's `∀ order` ruling actually ranges over — so
this definition is how a WITNESS is extracted, and correctness is the
separate `∀ order` obligation over the 7 sites `docs/c23-spec-mirror.md`
§5.3 measured. Writing the canonical order down is what makes that
obligation STATABLE; it does not discharge it, and nothing here should be
read as if it did.

The measure is `2 * Expr.sizes es + 2`, and the `+ 2` is load-bearing:
the head step must beat `evalExpr`'s `2 * e.size + 1` for a list whose
tail is empty, and the tail step needs `0 < e.size` — which is why
`Expr.size_pos` had to come back. -/
def evalArgs (ctx : Ctx) : List Expr → EvalM (List CVal)
  | [] => pure []
  | e :: es => do
      let v ← evalExpr ctx e
      let vs ← evalArgs ctx es
      pure (v :: vs)
  termination_by es => 2 * Expr.sizes es + 2
  decreasing_by all_goals (simp_wf <;> omega)

/-- §6.5.3.4 — the ADDRESS of `base.field` / `base->field`.

Takes `base` — a strict SUBTERM — rather than the reassembled node. The
node this replaces was rebuilt as `.member base field arrow ty sp`, which
is not a subterm of anything, and that is what defeated the recursion. -/
def memberAddr (ctx : Ctx) (base : Expr) (field : String) (arrow : Bool) : EvalM Ptr := do
  let basePtr ← if arrow then (do let v ← evalExpr ctx base; asPtr v)
                else evalLValue ctx base
  match ctx.layout.fieldOff base.ty field with
  | some off => pure (Mem.member basePtr off)
  | none => refuseUnsupported s!"no layout for field '{field}'"
  termination_by 2 * base.size + 2
  decreasing_by all_goals (simp_wf <;> omega)

/-- §6.5.3.2p2 — the ADDRESS of `base[idx]`. Same discipline: the parts,
never the rebuilt node. -/
def indexAddr (ctx : Ctx) (base idx : Expr) (ty : CType) : EvalM Ptr := do
  let bv ← evalExpr ctx base
  let bp ← asPtr bv
  let iv ← evalExpr ctx idx
  let (_, i) ← asInt iv
  match ctx.layout.size ty with
  | some esz => readMem (fun m => Mem.subscript m bp esz i)
  | none => refuseUnsupported s!"no size for element type '{ty}'"
  termination_by 2 * (base.size + idx.size) + 2
  decreasing_by all_goals (simp_wf <;> omega)

end

/-! ### The termination argument, STATED

`docs/backlog/c.md` 2026-08-23-c-5: **a green build is not a termination
argument.** Inch 3 built green with `evalExpr` REBUILDING its
`.member`/`.index` nodes — which are not subterms — and it only worked
because structural inference had slack elsewhere. Inch 5 removed the
slack and the whole block fell over, exposing a defect that had been
latent through three landings.

So the measure is written down rather than inferred. `Expr.size` counts
expression nodes (`Ast.lean`); the main pair carries `2 * size + 1` and
the address helpers `2 * size + 2`, so a helper is strictly smaller than
the node that called it and strictly larger than the subterms it
evaluates. The doubling is what buys room for that middle rung. -/
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
    Except.bind, Except.pure,
    hl, truthy, ofBool, pure, ExceptT.pure, StateT.pure]

/-- §6.5.15p4 — `||` is the mirror: a TRUE left operand answers 1 in the
left operand's own out-memory, and the right operand is not evaluated. -/
theorem or_shortCircuits (ctx : Ctx) (l r : Expr) (ty : CType) (sp : CSpan)
    (m m' : Mem) (t : IntTy) (n : Int) (hn : n ≠ 0)
    (hl : EvalM.run m (evalExpr ctx l) = .ok (.ok (.int t n), m')) :
    EvalM.run m (evalExpr ctx (.binop "||" l r ty sp)) = .ok (.ok (ofBool true), m') := by
  simp only [EvalM.run, StateT.run] at hl ⊢
  simp [evalExpr, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, bind, StateT.bind,
    Except.bind, Except.pure,
    hl, hn, truthy, ofBool, pure, ExceptT.pure, StateT.pure]

/-- §6.5.16p4 — `?:` evaluates EXACTLY ONE arm, and the theorem names
only the arm that ran. -/
theorem cond_takesOneArm (ctx : Ctx) (c t e : Expr) (ty : CType) (sp : CSpan)
    (m m' : Mem) (it : IntTy)
    (hc : EvalM.run m (evalExpr ctx c) = .ok (.ok (.int it 0), m')) :
    EvalM.run m (evalExpr ctx (.cond c t e ty sp)) = EvalM.run m' (evalExpr ctx e) := by
  simp only [EvalM.run, StateT.run] at hc ⊢
  simp [evalExpr, ExceptT.bind, ExceptT.bindCont, ExceptT.mk, bind, StateT.bind,
    Except.bind, Except.pure,
    hc, truthy, pure, ExceptT.pure, StateT.pure]

#print axioms and_shortCircuits
#print axioms or_shortCircuits
#print axioms cond_takesOneArm

/-! ## RUNG A — §6.5.3.3p10 / `J.1(16)`: PURITY, and the half of the ∀-order
obligation a syntax check can pay

`docs/c23-spec-mirror.md` §5.3 states the `J.1(16)` obligation per call
site as *"can this callee write what these siblings read"*. That is a
CONJUNCTION, and only its second half needs an effect summary:

1. **the siblings do not WRITE** — decidable from the term, and this
   section;
2. the one effectful argument does not write what the siblings READ —
   the effect-summary argument, which is **Rung B and is not claimed
   anywhere below.**

**The measurement is why (1) is worth landing on its own.** Over the
ingested corpus, gated in `Examples/c/sunfish/expr.lean` and reached
independently by `harness/c_construct_census.py`: of **320** call sites,
**215** take two or more arguments, and **208 of those 215 have EVERY
argument pure** — so at 208 of 215 multi-argument sites the ∀-order
obligation needs no effect summary at all: no order can differ, because
no order can write. The residue is exactly the **7** sites §5.3 already
names, and at none of them do two arguments carry an effect. **The
predicate that prices Rung B is the same predicate that cuts its domain
from 215 sites to 7.**

**`isPure` is an OVER-approximation, deliberately.** It is `nodeIsPure` at
EVERY node of the term — through `Expr.subexprs`, so it introduces no new
recursion, exactly as `Expr.size` does not — which means it calls an
expression impure whenever a write-capable node occurs anywhere inside
it, including under a `&&` that would never run it and under a `sizeof`
whose operand §6.5.4.4p2 does not evaluate at all. A sharper predicate
exists and is not needed: soundness is what the theorem consumes, and the
census says the coarseness costs nothing here — **the only impure node
kind occurring inside any call argument anywhere in the corpus is a
CALL** (10 occurrences), so the slack misclassifies no argument.

**What `isPure` is NOT.** It is not "has no observable effect". An
out-of-tier node is classified IMPURE even though this evaluator refuses
it, because *"the model declines"* is not *"the construct does not
write"*, and a predicate that pooled the two would silently become
unsound the day the construct is modelled. Likewise `initList` and
`compoundLit`, whose §6.7.11 semantics WRITES through the layout
(`docs/backlog/c.md` 2026-08-23-c-3). -/

/-- The write-capable NODE kinds, and nothing about their operands.

Read this against `evalExpr`'s clauses one for one: `storeAt` is reached
from exactly three of them — simple assignment (§6.5.17.2), compound
assignment (§6.5.17.3) and the increments (§6.5.3.5) — and `Ctx.call`
hands control to a handler this tier cannot see inside. Every other
clause in the block reaches memory only through `readMem`. -/
def Expr.nodeIsPure : Expr → Bool
  -- §6.5.17.2 — the store is `=`, and only `=`. Every other binary
  -- operator, `&&`/`||`/`,` included, is a value computation.
  | .binop op _ _ _ _ => op != "="
  -- §6.5.3.5 — measured: all 63 increment sites in the corpus are postfix,
  -- and both spellings write.
  | .unop op _ _ _ _ => op != "++" && op != "--"
  -- §6.5.17.3 — `a op= b` stores.
  | .compoundAssign .. => false
  -- §6.5.3.3 — an opaque callee. This is the constructor that makes the
  -- J.1(16) domain non-empty, and inch 5's repair is what made it REACHABLE.
  | .call .. => false
  -- §6.7.11 — aggregate initialization writes through the layout.
  | .initList .. | .compoundLit .. => false
  -- Out of tier: unknown, therefore not pure.
  | .unsupported .. => false
  | _ => true

/-- An expression whose evaluation cannot change memory — `nodeIsPure` at
every node, itself included.

Stated through `Expr.subexprs` so that it introduces **no new recursion**:
the nested `List Expr` under `call` and `initList` is elaborated there,
once, which is the same reason `Expr.size` is defined that way
(`LeanModels/C/Ast.lean`). -/
def Expr.isPure (e : Expr) : Bool := e.subexprs.all Expr.nodeIsPure

/-! ### Reading a purity fact off a node

One general lemma for the HEAD, and one extraction per constructor the
evaluator recurses into. Only the forward direction is ever needed, which
is why none of these is stated as an equivalence. -/

/-- Every `subexprs` clause emits `e` itself, so a pure term has a pure
head. -/
theorem Expr.nodeIsPure_of_isPure {e : Expr} (h : Expr.isPure e = true) :
    Expr.nodeIsPure e = true := by
  cases e <;>
    simp_all [Expr.isPure, Expr.subexprs, Expr.nodeIsPure, List.all_cons, List.all_append]

theorem Expr.isPure_paren {s : Expr} {t : CType} {sp : CSpan}
    (h : Expr.isPure (.paren s t sp) = true) : Expr.isPure s = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, Bool.and_eq_true] at h ⊢
  exact h.2

theorem Expr.isPure_implicitCast {ck : String} {s : Expr} {t : CType} {sp : CSpan}
    (h : Expr.isPure (.implicitCast ck s t sp) = true) : Expr.isPure s = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, Bool.and_eq_true] at h ⊢
  exact h.2

theorem Expr.isPure_cast {ck : String} {s : Expr} {t : CType} {sp : CSpan}
    (h : Expr.isPure (.cast ck s t sp) = true) : Expr.isPure s = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, Bool.and_eq_true] at h ⊢
  exact h.2

theorem Expr.isPure_member {b : Expr} {f : String} {a : Bool} {t : CType} {sp : CSpan}
    (h : Expr.isPure (.member b f a t sp) = true) : Expr.isPure b = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, Bool.and_eq_true] at h ⊢
  exact h.2

theorem Expr.isPure_unop {op : String} {s : Expr} {post : Bool} {t : CType} {sp : CSpan}
    (h : Expr.isPure (.unop op s post t sp) = true) : Expr.isPure s = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, Bool.and_eq_true] at h ⊢
  exact h.2

theorem Expr.isPure_index_base {b i : Expr} {t : CType} {sp : CSpan}
    (h : Expr.isPure (.index b i t sp) = true) : Expr.isPure b = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, List.all_append,
    Bool.and_eq_true] at h ⊢
  exact h.2.1

theorem Expr.isPure_index_idx {b i : Expr} {t : CType} {sp : CSpan}
    (h : Expr.isPure (.index b i t sp) = true) : Expr.isPure i = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, List.all_append,
    Bool.and_eq_true] at h ⊢
  exact h.2.2

theorem Expr.isPure_binop_l {op : String} {l r : Expr} {t : CType} {sp : CSpan}
    (h : Expr.isPure (.binop op l r t sp) = true) : Expr.isPure l = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, List.all_append,
    Bool.and_eq_true] at h ⊢
  exact h.2.1

theorem Expr.isPure_binop_r {op : String} {l r : Expr} {t : CType} {sp : CSpan}
    (h : Expr.isPure (.binop op l r t sp) = true) : Expr.isPure r = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, List.all_append,
    Bool.and_eq_true] at h ⊢
  exact h.2.2

theorem Expr.isPure_cond_c {c a b : Expr} {t : CType} {sp : CSpan}
    (h : Expr.isPure (.cond c a b t sp) = true) : Expr.isPure c = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, List.all_append,
    Bool.and_eq_true] at h ⊢
  exact h.2.1.1

theorem Expr.isPure_cond_t {c a b : Expr} {t : CType} {sp : CSpan}
    (h : Expr.isPure (.cond c a b t sp) = true) : Expr.isPure a = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, List.all_append,
    Bool.and_eq_true] at h ⊢
  exact h.2.1.2

theorem Expr.isPure_cond_e {c a b : Expr} {t : CType} {sp : CSpan}
    (h : Expr.isPure (.cond c a b t sp) = true) : Expr.isPure b = true := by
  simp only [Expr.isPure, Expr.subexprs, List.all_cons, List.all_append,
    Bool.and_eq_true] at h ⊢
  exact h.2.2

/-! ### THE RUN SEAM — ADOPTED FROM `Core`, not restated here

This tier used to carry its own `run_bind` and its four step lemmas. They
are gone: `LeanModels/Core/Outcome.lean` §4 now holds them, generic in all
four of `SemMWith`'s parameters, and this file uses `SemMWith.run_bind`,
`run_bind_ok`, `run_bind_loud`, `run_bind_raise`, `run_pure`, `run_get`
and `run_throw` directly.

**The lift is what the convergence asked for and the paragraph that
carried it is deleted with it.** `2026-08-24-c-12` recorded that
`LeanModels/Go/Obs.lean` §1 had the same seam for `GoM`, that `GoM` and
`EvalM` are both `SemMWith`, and that the two proofs differed only by four
type substitutions — and it said the lift was a spine landing to be
priced rather than taken from a tier commit. It has now been taken, so
the note describing the duplication has no subject left.

> **A paragraph that exists to make a duplication visible is deleted by
> the commit that removes the duplication — carrying it afterwards
> documents a state the tree is no longer in.**

**One row stays, and it is genuinely this tier's.** `refuseUnsupported`
captures the memory AS IT STOOD at the refusal site — `fun m => .error (…
(some m))` — which is not Core's `refuseWith`, whose snapshot is a fixed
argument. §3.4's ruling put the capture in the primitive so no call site
can forget it; that makes the primitive C's, and so is its row. -/

section Seam
variable {α : Type}

/-- An out-of-tier refusal answers in the `Halt` BASE and carries the
memory it found, so there is no `.ok` for it to produce at all. Not
Core's `run_refuseWith`: the snapshot here is CAPTURED, not passed. -/
theorem EvalM.run_refuseUnsupported (what : String) (m : Mem) :
    (refuseUnsupported what : EvalM α) m
      = .error (.unsupported (.unsupported ()) what (some m)) := rfl

end Seam

/-! ### MEMORY INVARIANCE, and the algebra that makes it cheap -/

/-- A computation that cannot change memory: **whatever it answers**, the
memory it hands back is the memory it was handed.

The quantifier ranges over `r : Except Refusal α`, so this covers the
refusal branch too — which is not decoration. `ExceptT` OUTSIDE `StateT`
is the state-RETAINING order (`LeanModels/Core/Outcome.lean`), so a
refusal carries a memory, and a predicate that spoke only about success
would say nothing about the branch the layer order exists to keep
world-aware.

**A STRUCTURE, not a `def` returning `∀`, and the difference cost a
tenure.** As a `def` it unfolded under `intro` — so the closing tactic's
`intro` fired on `MemInvariant (…)` itself, stripped the predicate to a
raw `m' = m`, and every subsequent `apply` matched that instead of the
computation. Thirteen goals, one cause. A structure is opaque to `intro`
by construction, which is the property the tactic actually depends on.

> **A tactic that dispatches on a goal's HEAD needs the head to be
> stable; a `def` that unfolds to a binder has no stable head.** -/
structure MemInvariant {α : Type} (x : EvalM α) : Prop where
  /-- Whatever `x` answers, it hands back the memory it was handed. -/
  out : ∀ (m : Mem) (r : Except Refusal α) (m' : Mem), x m = .ok (r, m') → m' = m

namespace MemInvariant

variable {α β : Type}

theorem pure' (a : α) : MemInvariant (pure a : EvalM α) := by
  constructor
  intro m r m' h
  rw [SemMWith.run_pure] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  exact h.2.symm

theorem get' : MemInvariant (get : EvalM Mem) := by
  constructor
  intro m r m' h
  rw [SemMWith.run_get] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  exact h.2.symm

theorem throw' (e : Refusal) : MemInvariant (throw e : EvalM α) := by
  constructor
  intro m r m' h
  rw [SemMWith.run_throw] at h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  exact h.2.symm

theorem refuseUB' (f : MemFault) : MemInvariant (refuseUB f : EvalM α) := throw' (.memUB f)
theorem refuseValue' (u : UB) : MemInvariant (refuseValue u : EvalM α) := throw' (.valueUB u)
theorem refuseLibc' (n : String) : MemInvariant (refuseLibc n : EvalM α) := throw' (.libc n)

theorem refuseUnsupported' (what : String) :
    MemInvariant (refuseUnsupported what : EvalM α) := by
  constructor
  intro m r m' h
  rw [EvalM.run_refuseUnsupported] at h
  simp at h

/-- The composition rule, and the refusal branch is where the layer order
becomes visible: the head's out-memory is `m` by `hx` applied **to the
refusal result**, which is exactly the quantifier `MemInvariant` carries. -/
theorem bind {x : EvalM α} {f : α → EvalM β}
    (hx : MemInvariant x) (hf : ∀ a, MemInvariant (f a)) : MemInvariant (x >>= f) := by
  constructor
  intro m r m' h
  cases hxm : x m with
  | error l =>
      rw [SemMWith.run_bind_loud hxm] at h
      simp at h
  | ok p =>
      obtain ⟨r₀, m₀⟩ := p
      have hm₀ : m₀ = m := hx.out m r₀ m₀ hxm
      cases r₀ with
      | error e =>
          rw [SemMWith.run_bind_raise hxm] at h
          simp only [Except.ok.injEq, Prod.mk.injEq] at h
          exact h.2.symm.trans hm₀
      | ok a =>
          rw [SemMWith.run_bind_ok hxm] at h
          exact ((hf a).out m₀ r m' h).trans hm₀

/-- `map` needs no second opening: it is `pure`-after-`bind`. Present
because `simp` normalizes `x >>= fun a => pure (g a)` into `g <$> x`, so a
goal that started as a bind can arrive here wearing the other spelling. -/
theorem map' {x : EvalM α} (g : α → β) (hx : MemInvariant x) :
    MemInvariant (g <$> x) := by
  rw [map_eq_pure_bind]
  exact bind hx fun _ => pure' _

/-- Reading is invariant, and outside `storeAt` it is the ONLY way this
block reaches memory at all. -/
theorem readMem' (f : Mem → MRes α) : MemInvariant (readMem f) := by
  refine bind get' fun m0 => ?_
  cases f m0 with
  | ok a => exact pure' a
  | error e => exact throw' e

theorem intTyOf' (ty : CType) : MemInvariant (intTyOf ty) := by
  first | simp only [intTyOf] | rw [intTyOf.eq_def]
  split
  · exact pure' _
  · exact refuseUnsupported' _

theorem truthy' (v : CVal) : MemInvariant (truthy v) := by
  cases v <;> first | exact pure' _ | exact refuseUB' _

theorem asPtr' (v : CVal) : MemInvariant (asPtr v) := by
  cases v <;> first | exact pure' _ | exact refuseUnsupported' _ | exact refuseUB' _

theorem asInt' (v : CVal) : MemInvariant (asInt v) := by
  cases v <;> first | exact pure' _ | exact refuseUnsupported' _ | exact refuseUB' _

theorem loadAt' (p : Ptr) (ty : CType) : MemInvariant (loadAt p ty) := by
  first | simp only [loadAt] | rw [loadAt.eq_def]
  split
  · exact bind (readMem' _) fun _ => pure' _
  · exact bind (intTyOf' _) fun _ => readMem' _

theorem intBinop' (op : String) (t : IntTy) (a b : Int) :
    MemInvariant (intBinop op t a b) := by
  first | simp only [intBinop] | rw [intBinop.eq_def]
  repeat (any_goals split)
  all_goals first
    | exact pure' _
    | exact refuseValue' _
    | exact refuseUB' _
    | exact refuseUnsupported' _

theorem evalArith' (ctx : Ctx) (op : String) (lv rv : CVal) (ty : CType) :
    MemInvariant (evalArith ctx op lv rv ty) := by
  cases lv <;> cases rv <;>
    first | simp only [evalArith] | rw [evalArith.eq_def]
  repeat (any_goals split)
  all_goals first
    | exact pure' _
    | exact refuseValue' _
    | exact refuseUB' _
    | exact refuseUnsupported' _
    | exact intBinop' _ _ _ _
    | exact bind (readMem' _) fun _ => pure' _

end MemInvariant

/-- Close a `MemInvariant` goal for a computation assembled out of the
memory-READING primitives alone.

Nothing here can unfold a recursive function by accident: the five
functions of the mutual block are well-founded definitions and therefore
irreducible, so an `evalExpr` obligation is closed by `assumption` from an
induction hypothesis, or it is not closed at all.

**Every `apply` runs `with_reducible`, and that is a COST fix, not a
style one.** At default transparency a failing `apply MemInvariant.evalArith'`
delta-unfolds `evalArith` and matches its nineteen-way `String` match
against the goal before giving up — a search this tactic runs at every one
of its steps, on every goal. Tenure 2 died of it: two `(deterministic)
timeout at whnf` errors on the two arms whose goals carry the deepest
terms (`sizeof`'s `Option.bind` through an opaque `Layout` field, and a
`String.toInt?`). At reducible transparency each of these lemmas matches
only when the goal's head IS the constant it names, so every failure is
one comparison instead of one unfolding.

> **A tactic assembled from `first | apply …` pays its whole alternative
> list at DEFAULT transparency on every goal; if the alternatives name
> non-reducible constants, the list is a search over their bodies.**

**`contradiction` is in the list for the UNREACHABLE arms.** When a clause
is opened through `eq_def` rather than its per-clause equation, `split`
produces one goal per arm of the WHOLE match — nineteen of which carry a
hypothesis equating two different constructors. They are not hard goals;
they simply have to be recognised as impossible, and `contradiction` is
the tactic that does it by `noConfusion`. Without it a fallback path that
opens more than it needs to leaves goals nothing else in the list can
speak to. -/
macro "mem_inv" : tactic => `(tactic|
  repeat (any_goals (first
    | assumption
    | contradiction
    | (with_reducible apply MemInvariant.pure')
    | (with_reducible apply MemInvariant.get')
    | (with_reducible apply MemInvariant.throw')
    | (with_reducible apply MemInvariant.refuseUB')
    | (with_reducible apply MemInvariant.refuseValue')
    | (with_reducible apply MemInvariant.refuseLibc')
    | (with_reducible apply MemInvariant.refuseUnsupported')
    | (with_reducible apply MemInvariant.readMem')
    | (with_reducible apply MemInvariant.intTyOf')
    | (with_reducible apply MemInvariant.truthy')
    | (with_reducible apply MemInvariant.asPtr')
    | (with_reducible apply MemInvariant.asInt')
    | (with_reducible apply MemInvariant.loadAt')
    | (with_reducible apply MemInvariant.intBinop')
    | (with_reducible apply MemInvariant.evalArith')
    | (with_reducible apply MemInvariant.bind)
    | (with_reducible apply MemInvariant.map')
    | (simp only [letFun])
    | intro _
    | split)))

/-- Open `evalExpr`'s clause at a KNOWN head. Two spellings because Lean
generates per-clause equations where the patterns are constructors and a
GUARDED default where they are not, and only one of the two fires in each
case; if neither opens the clause the proof below fails loudly. -/
macro "open_eval" : tactic => `(tactic| first | simp only [evalExpr] | rw [evalExpr.eq_def])

/-- The same for `evalLValue`, whose catch-all *is* the guarded default. -/
macro "open_lvalue" : tactic => `(tactic| first | simp only [evalLValue] | rw [evalLValue.eq_def])

/-! ### The address helpers

Stated with their sub-evaluations' invariance as HYPOTHESES, so neither
needs an induction of its own: both take strict SUBTERMS, which is the
same property that made the termination measure work. -/

theorem MemInvariant.memberAddr' {ctx : Ctx} {base : Expr} {field : String} {arrow : Bool}
    (hv : MemInvariant (evalExpr ctx base)) (hl : MemInvariant (evalLValue ctx base)) :
    MemInvariant (memberAddr ctx base field arrow) := by
  first | simp only [memberAddr] | rw [memberAddr.eq_def]
  mem_inv

theorem MemInvariant.indexAddr' {ctx : Ctx} {base idx : Expr} {ty : CType}
    (hb : MemInvariant (evalExpr ctx base)) (hi : MemInvariant (evalExpr ctx idx)) :
    MemInvariant (indexAddr ctx base idx ty) := by
  first | simp only [indexAddr] | rw [indexAddr.eq_def]
  mem_inv

/-! ### THE THEOREM

Strong induction on `Expr.size`, and the two functions are proved TOGETHER
because they are defined together. `evalArgs` never appears: `nodeIsPure`
makes a `call` node impure, so the arm that would reach it is vacuous —
which is the honest shape, since a call is precisely what this theorem
cannot speak for. -/

-- A twenty-constructor case analysis, each arm running a tactic search: the
-- default 200 000 is a PER-DECLARATION budget sized for ordinary proofs, and
-- this declaration is twenty of them. The budget is not the fix — the fix is
-- `mem_inv`'s `with_reducible`, which is what made the search cheap; this only
-- stops the sum of twenty cheap searches from hitting a single-proof ceiling.
set_option maxHeartbeats 1000000 in
private theorem memInvariant_core (ctx : Ctx) : ∀ (n : Nat) (e : Expr), e.size ≤ n →
    Expr.isPure e = true →
    MemInvariant (evalExpr ctx e) ∧ MemInvariant (evalLValue ctx e) := by
  intro n
  induction n with
  | zero =>
      intro e he _
      exact absurd (Expr.size_pos e) (by omega)
  | succ n ih =>
      intro e he hp
      have hnode := Expr.nodeIsPure_of_isPure hp
      cases e with
      | intLit _ _ _ => exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | charLit _ _ _ => exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | strLit _ _ _ => exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | floatLit _ _ _ => exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | declRef _ _ _ _ => exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | typeTrait _ _ _ _ _ => exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | constExpr _ _ _ _ => exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | paren s _ _ =>
          obtain ⟨i1, i2⟩ := ih s (by simp only [Expr.size_paren] at he; omega)
            (Expr.isPure_paren hp)
          exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | implicitCast _ s _ _ =>
          obtain ⟨i1, i2⟩ := ih s (by simp only [Expr.size_implicitCast] at he; omega)
            (Expr.isPure_implicitCast hp)
          exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | cast _ s _ _ =>
          obtain ⟨i1, i2⟩ := ih s (by simp only [Expr.size_cast] at he; omega)
            (Expr.isPure_cast hp)
          exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | member b f a _ _ =>
          obtain ⟨i1, i2⟩ := ih b (by simp only [Expr.size_member] at he; omega)
            (Expr.isPure_member hp)
          have hma : MemInvariant (memberAddr ctx b f a) := MemInvariant.memberAddr' i1 i2
          exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | index b i ty _ =>
          obtain ⟨b1, _⟩ := ih b (by simp only [Expr.size_index] at he; omega)
            (Expr.isPure_index_base hp)
          obtain ⟨i1, _⟩ := ih i (by simp only [Expr.size_index] at he; omega)
            (Expr.isPure_index_idx hp)
          have hia : MemInvariant (indexAddr ctx b i ty) := MemInvariant.indexAddr' b1 i1
          exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | cond cc tt ee _ _ =>
          obtain ⟨c1, _⟩ := ih cc (by simp only [Expr.size_cond] at he; omega)
            (Expr.isPure_cond_c hp)
          obtain ⟨t1, _⟩ := ih tt (by simp only [Expr.size_cond] at he; omega)
            (Expr.isPure_cond_t hp)
          obtain ⟨e1, _⟩ := ih ee (by simp only [Expr.size_cond] at he; omega)
            (Expr.isPure_cond_e hp)
          exact ⟨by open_eval; mem_inv, by open_lvalue; mem_inv⟩
      | binop op l r _ _ =>
          obtain ⟨l1, _⟩ := ih l (by simp only [Expr.size_binop] at he; omega)
            (Expr.isPure_binop_l hp)
          obtain ⟨r1, _⟩ := ih r (by simp only [Expr.size_binop] at he; omega)
            (Expr.isPure_binop_r hp)
          simp only [Expr.nodeIsPure] at hnode
          refine ⟨?_, by open_lvalue; mem_inv⟩
          -- The `=` arm is the one clause of this constructor that stores,
          -- and `hnode` is exactly the fact that excludes it.
          open_eval
          repeat (any_goals split)
          all_goals first | (mem_inv; done) | simp_all
      | unop op s post _ _ =>
          obtain ⟨s1, s2⟩ := ih s (by simp only [Expr.size_unop] at he; omega)
            (Expr.isPure_unop hp)
          simp only [Expr.nodeIsPure] at hnode
          constructor
          · -- `++`/`--` store; `hnode` excludes both spellings.
            open_eval
            repeat (any_goals split)
            all_goals first | (mem_inv; done) | simp_all
          · open_lvalue
            repeat (any_goals split)
            all_goals first | (mem_inv; done) | simp_all
      -- The five impure heads. Each arm is vacuous, and each is vacuous for
      -- a DIFFERENT reason worth keeping: a call is opaque; an assignment
      -- and an increment store; aggregate initialization writes through the
      -- layout; an out-of-tier node is unknown rather than harmless.
      | call _ _ _ _ => simp [Expr.nodeIsPure] at hnode
      | compoundAssign _ _ _ _ _ => simp [Expr.nodeIsPure] at hnode
      | initList _ _ _ => simp [Expr.nodeIsPure] at hnode
      | compoundLit _ _ _ => simp [Expr.nodeIsPure] at hnode
      | unsupported _ _ _ => simp [Expr.nodeIsPure] at hnode

/-- **RUNG A.** A pure expression's evaluation leaves memory exactly as it
found it — on the value branch AND on the refusal branch. -/
theorem evalExpr_memInvariant (ctx : Ctx) (e : Expr) (h : Expr.isPure e = true) :
    MemInvariant (evalExpr ctx e) :=
  (memInvariant_core ctx e.size e (Nat.le_refl _) h).1

/-- The same in LVALUE position: taking an address does not write either. -/
theorem evalLValue_memInvariant (ctx : Ctx) (e : Expr) (h : Expr.isPure e = true) :
    MemInvariant (evalLValue ctx e) :=
  (memInvariant_core ctx e.size e (Nat.le_refl _) h).2

/-- **The `J.1(16)`-facing corollary**: an argument LIST whose every member
is pure is evaluated without touching memory. At a call site whose
siblings are pure, the effectful argument is therefore the only writer —
whichever order §6.5.3.3p10 lets the implementation choose.

That is the SIBLING half, and it is the half a syntax check decides. The
other half — that the one effectful argument does not write what the
siblings READ — is Rung B, and nothing here is evidence for it. -/
theorem evalArgs_memInvariant (ctx : Ctx) : ∀ (es : List Expr),
    es.all Expr.isPure = true → MemInvariant (evalArgs ctx es) := by
  intro es
  induction es with
  | nil =>
      intro _
      first | simp only [evalArgs] | rw [evalArgs.eq_def]
      exact MemInvariant.pure' _
  | cons e es ihs =>
      intro h
      simp only [List.all_cons, Bool.and_eq_true] at h
      first | simp only [evalArgs] | rw [evalArgs.eq_def]
      exact MemInvariant.bind (evalExpr_memInvariant ctx e h.1) fun _ =>
        MemInvariant.bind (ihs h.2) fun _ => MemInvariant.pure' _


/-! ## RUNG B — §6.5.3.3p10 / `J.1(16)`: the order becomes a PARAMETER, and
the 208 fall

Rung A proved that a pure expression does not WRITE. This section spends
that, and the spending splits the same way the obligation does:

* **the 208 multi-argument sites whose every argument is pure** — settled
  here, unconditionally. The argument is short once purity is in hand:
  memory never changes, so every argument's value is a function of the
  memory the CALL started in, and a function of that memory cannot depend
  on when it was applied;
* **the 7** — one nested call each, and whether it writes what its
  siblings read. That is an effect summary, it is **not** proved here, and
  it appears below as a NAMED hypothesis with a theorem saying exactly
  what discharging it buys.

**THE ORDER PARAMETER TURNED OUT NOT TO NEED A TAGGED EVALUATOR.** The
plan was an `evalArgsAt` over position-tagged arguments, so that two
orders could be compared. Purity makes it unnecessary: once every argument
is a function of ONE memory, "the value of argument `i`" is
`valOf? ctx m eᵢ` no matter which walk produced it, and the ∀-order
statement is about `List.Perm` directly. The tagging existed to carry
information across the reordering, and Rung A had already made that
information order-free.

> **A parameter you were going to thread is a sign the property is not yet
> stated at the right level: when the order stops being observable, the
> machinery for observing it stops being needed.**

**AND THE OBSERVABLE IS THE ANSWER, NEVER THE RUN.** Every theorem below
takes the canonical run's success as a HYPOTHESIS rather than assuming it
in prose, and that is not fussiness. Two orders can disagree about *which
refusal is reported* whenever more than one argument would refuse —
`f(g(), h())` with both refusing answers with `g`'s cause left-to-right
and `h`'s right-to-left, and §3.1 never pools the causes, so the
difference is visible in the verdict.

> **Order-independence is a property of the VALUE and the MEMORY, never of
> the trace: a ∀-order theorem quantified over the run would be false for
> a reason that has nothing to do with sequencing.** -/

/-- The value an expression yields at a given memory, or `none` if it
yields none — it refused, or the model halted.

This is the function the whole ∀-order argument turns on. `evalExpr ctx e`
IS a function of the memory it is handed, so if the memory is the same
then so is the answer, and *when* the argument ran cannot enter into it.
Saying that requires naming the function. -/
def valOf? (ctx : Ctx) (m : Mem) (e : Expr) : Option CVal :=
  match evalExpr ctx e m with
  | .ok (.ok v, _) => some v
  | _ => none

theorem valOf?_of_run {ctx : Ctx} {m m' : Mem} {e : Expr} {v : CVal}
    (h : evalExpr ctx e m = .ok (.ok v, m')) : valOf? ctx m e = some v := by
  simp only [valOf?, h]

/-- The converse, **for a pure expression**, and purity is exactly what
makes it a converse rather than something weaker: it pins the out-memory
to the in-memory, so the whole run can be reconstructed and not just its
value. -/
theorem run_of_valOf? {ctx : Ctx} {m : Mem} {e : Expr} {v : CVal}
    (hp : Expr.isPure e = true) (h : valOf? ctx m e = some v) :
    evalExpr ctx e m = .ok (.ok v, m) := by
  rw [valOf?] at h
  split at h
  · rename_i v₀ m₀ heq
    have hm : m₀ = m := (evalExpr_memInvariant ctx e hp).out m _ m₀ heq
    simp only [Option.some.injEq] at h
    subst h
    subst hm
    exact heq
  · simp at h

/-! ### The argument walk, opened once

Two lemmas — build a `cons` step and take one apart — so that neither
theorem below has to unfold the monad again. This is `Core` §4's discipline
one level up: **one opening, and the rest are corollaries.** -/

theorem evalArgs_nil (ctx : Ctx) (m : Mem) :
    evalArgs ctx [] m = .ok (.ok [], m) := by
  simp only [evalArgs]
  exact SemMWith.run_pure _ _

theorem evalArgs_cons_ok {ctx : Ctx} {e : Expr} {es : List Expr} {m m₀ m₁ : Mem}
    {v : CVal} {vs : List CVal}
    (he : evalExpr ctx e m = .ok (.ok v, m₀))
    (hes : evalArgs ctx es m₀ = .ok (.ok vs, m₁)) :
    evalArgs ctx (e :: es) m = .ok (.ok (v :: vs), m₁) := by
  simp only [evalArgs]
  rw [SemMWith.run_bind_ok he, SemMWith.run_bind_ok hes, SemMWith.run_pure]

/-- Taking a successful walk apart: the head ran, the tail ran from where
the head left off, and the answer is their cons. **A successful `cons` has
no other shape** — which is what makes the case analysis below a case
analysis rather than a guess. -/
theorem evalArgs_cons_inv {ctx : Ctx} {e : Expr} {es : List Expr} {m m₁ : Mem}
    {vs' : List CVal} (h : evalArgs ctx (e :: es) m = .ok (.ok vs', m₁)) :
    ∃ (v : CVal) (m₀ : Mem) (vs : List CVal),
      evalExpr ctx e m = .ok (.ok v, m₀) ∧ evalArgs ctx es m₀ = .ok (.ok vs, m₁)
        ∧ vs' = v :: vs := by
  simp only [evalArgs] at h
  cases he : evalExpr ctx e m with
  | error l => rw [SemMWith.run_bind_loud he] at h; simp at h
  | ok pr =>
      obtain ⟨r, m₀⟩ := pr
      cases r with
      | error r' => rw [SemMWith.run_bind_raise he] at h; simp at h
      | ok v =>
          rw [SemMWith.run_bind_ok he] at h
          cases hts : evalArgs ctx es m₀ with
          | error l => rw [SemMWith.run_bind_loud hts] at h; simp at h
          | ok pr2 =>
              obtain ⟨r2, m₂⟩ := pr2
              cases r2 with
              | error r2' => rw [SemMWith.run_bind_raise hts] at h; simp at h
              | ok tvs =>
                  rw [SemMWith.run_bind_ok hts, SemMWith.run_pure] at h
                  simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨hl, hm⟩ := h
                  subst hm
                  subst hl
                  exact ⟨v, m₀, tvs, rfl, hts, rfl⟩

/-! ### The pointwise law — and it is the whole of the 208

An all-pure argument list is evaluated **at one memory**, the one the call
started in, however long the list is. So the list's answer is
`valOf? ctx m` applied pointwise, and nothing about the walk survives into
it. -/

/-- **THE POINTWISE LAW.** A pure argument list's values are `valOf? ctx m`
applied to it, at the INCOMING memory, and the memory comes back
untouched. -/
theorem evalArgs_pure_pointwise (ctx : Ctx) : ∀ (es : List Expr),
    es.all Expr.isPure = true → ∀ (m : Mem) (vs : List CVal) (m' : Mem),
      evalArgs ctx es m = .ok (.ok vs, m') →
        m' = m ∧ es.map (valOf? ctx m) = vs.map some := by
  intro es
  induction es with
  | nil =>
      intro _ m vs m' h
      rw [evalArgs_nil] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hl, hm⟩ := h
      subst hl
      exact ⟨hm.symm, rfl⟩
  | cons e es ih =>
      intro hp m vs m' h
      simp only [List.all_cons, Bool.and_eq_true] at hp
      obtain ⟨v, m₀, tvs, he, hts, hvs⟩ := evalArgs_cons_inv h
      have hm₀ : m₀ = m := (evalExpr_memInvariant ctx e hp.1).out m _ m₀ he
      rw [hm₀] at hts
      obtain ⟨htm, htv⟩ := ih hp.2 m tvs m' hts
      subst hvs
      exact ⟨htm, by simp only [List.map_cons, htv, valOf?_of_run he]⟩

/-- The converse at a GIVEN value list: a pure argument list whose values
`valOf? ctx m` supplies really does run to them, in whatever order it is
written. **This is the half that makes the claim about EVERY order** and
not only about the ones that happen to succeed. -/
theorem evalArgs_pure_ofPointwise (ctx : Ctx) : ∀ (es : List Expr),
    es.all Expr.isPure = true → ∀ (m : Mem) (vs : List CVal),
      es.map (valOf? ctx m) = vs.map some →
        evalArgs ctx es m = .ok (.ok vs, m) := by
  intro es
  induction es with
  | nil =>
      intro _ m vs h
      cases vs with
      | nil => exact evalArgs_nil ctx m
      | cons w ws => simp at h
  | cons e es ih =>
      intro hp m vs h
      simp only [List.all_cons, Bool.and_eq_true] at hp
      cases vs with
      | nil => simp at h
      | cons v ws =>
          simp only [List.map_cons, List.cons.injEq] at h
          exact evalArgs_cons_ok (run_of_valOf? hp.1 h.1) (ih hp.2 m ws h.2)

/-! ### ∀ ORDER, for the 208 -/

/-- **THE ∀-ORDER THEOREM for an all-pure argument list.** Any two orders
agree on the values — as multisets, which is what "the same arguments in a
different order" means — and both leave the memory they were handed.

`hperm` is an ARBITRARY permutation and the conclusion is an equation, so
this is the unconditional discharge of the **208 of 215** multi-argument
call sites whose every argument is pure. No effect summary appears, because
no effects do. -/
theorem evalArgs_orderIndependent (ctx : Ctx) {es fs : List Expr} {vs ws : List CVal}
    {m m₁ m₂ : Mem} (hperm : es.Perm fs) (hp : es.all Expr.isPure = true)
    (h₁ : evalArgs ctx es m = .ok (.ok vs, m₁))
    (h₂ : evalArgs ctx fs m = .ok (.ok ws, m₂)) :
    m₁ = m ∧ m₂ = m ∧ (vs.map some).Perm (ws.map some) := by
  have hpf : fs.all Expr.isPure = true := by
    simp only [List.all_eq_true] at hp ⊢
    intro x hx
    exact hp x (hperm.mem_iff.mpr hx)
  obtain ⟨hm₁, hv⟩ := evalArgs_pure_pointwise ctx es hp m vs m₁ h₁
  obtain ⟨hm₂, hw⟩ := evalArgs_pure_pointwise ctx fs hpf m ws m₂ h₂
  refine ⟨hm₁, hm₂, ?_⟩
  rw [← hv, ← hw]
  exact hperm.map _

/-- The two-argument instance, spelled out because **four of the seven
sites have arity two** and because it is the one shape where the other
order can be exhibited rather than merely compared: the swapped call runs,
and it runs to the swapped values. -/
theorem evalArgs_pair_swap (ctx : Ctx) (a b : Expr) {m m₁ : Mem} {va vb : CVal}
    (ha : Expr.isPure a = true) (hb : Expr.isPure b = true)
    (h : evalArgs ctx [a, b] m = .ok (.ok [va, vb], m₁)) :
    m₁ = m ∧ evalArgs ctx [b, a] m = .ok (.ok [vb, va], m) := by
  have hall : [a, b].all Expr.isPure = true := by
    simp only [List.all_cons, List.all_nil, Bool.and_eq_true]
    exact ⟨ha, hb, trivial⟩
  obtain ⟨hm, hv⟩ := evalArgs_pure_pointwise ctx [a, b] hall m [va, vb] m₁ h
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hv
  refine ⟨hm, evalArgs_pure_ofPointwise ctx [b, a] ?_ m [vb, va] ?_⟩
  · simp only [List.all_cons, List.all_nil, Bool.and_eq_true]
    exact ⟨hb, ha, trivial⟩
  · simp only [List.map_cons, List.map_nil, List.cons.injEq]
    exact ⟨hv.2.1, hv.1, trivial⟩

/-! ### THE 7 — the residue, as an OBLIGATION rather than a paragraph

At each of the seven sites `docs/c23-spec-mirror.md` §5.3 names, exactly
one argument is impure and it is a nested call. Rung A retires the
siblings' half; what remains is whether the callee writes what a sibling
READS, and this tier has no read-set.

So it is written down as a predicate, and the theorem below says exactly
what discharging it buys. That is inch 5's move reused: **make the
property statable about a function first, and the discharge becomes a
separate nameable step instead of a paragraph.** -/

/-- **THE EFFECT SUMMARY, as an obligation.** Running `x` leaves `e`'s
value alone.

Stated OBSERVATIONALLY, over `valOf?`, rather than as a footprint — because
the observable is what Thomas's ∀-order ruling quantifies over, and a
footprint would be a strictly stronger claim than the obligation needs. A
callee that writes a location the sibling reads and writes it back is
non-interfering here and would not be under a footprint reading; the
standard asks about the value, so this does too. -/
def NonInterfering {α : Type} (ctx : Ctx) (x : EvalM α) (e : Expr) : Prop :=
  ∀ (m : Mem) (a : α) (m' : Mem), x m = .ok (.ok a, m') → valOf? ctx m' e = valOf? ctx m e

/-- **WHAT THE EFFECT SUMMARY BUYS**, at the seven sites' shape: two
arguments, the first pure, the second doing whatever it likes.

Read which hypothesis carries which half. **`hp` is Rung A** — the pure
sibling does not write, so the call still starts from `m` when it runs
second, which is why `hec` can be stated at `m` at all. **`hni` is the
residue** — the call does not disturb what the sibling reads, so the
sibling still answers `vp` when it runs second. Neither implies the other
and the theorem needs both; that is the honest shape of a half-discharged
obligation. -/
theorem evalArgs_pair_oneEffect (ctx : Ctx) (p c : Expr) {m m₀ m₁ : Mem} {vp vc : CVal}
    (hp : Expr.isPure p = true) (hni : NonInterfering ctx (evalExpr ctx c) p)
    (hep : evalExpr ctx p m = .ok (.ok vp, m₀))
    (hec : evalExpr ctx c m = .ok (.ok vc, m₁)) :
    evalArgs ctx [p, c] m = .ok (.ok [vp, vc], m₁)
      ∧ evalArgs ctx [c, p] m = .ok (.ok [vc, vp], m₁) := by
  -- Rung A: the pure argument's out-memory IS its in-memory.
  have hm₀ : m₀ = m := (evalExpr_memInvariant ctx p hp).out m _ m₀ hep
  rw [hm₀] at hep
  refine ⟨evalArgs_cons_ok hep (evalArgs_cons_ok hec (evalArgs_nil ctx m₁)), ?_⟩
  -- The residue: after the call, the sibling still answers what it answered.
  have hsame : valOf? ctx m₁ p = some vp := by
    rw [hni m vc m₁ hec]
    exact valOf?_of_run hep
  exact evalArgs_cons_ok hec
    (evalArgs_cons_ok (run_of_valOf? hp hsame) (evalArgs_nil ctx m₁))

/-- **AND THE HALF THAT IS FREE.** A pure argument is non-interfering with
anything — including itself — so the seven sites' hypothesis is only ever
about the ONE impure argument. This is what makes the residue seven
obligations and not fourteen. -/
theorem nonInterfering_of_isPure {ctx : Ctx} {x : Expr} {e : Expr}
    (hx : Expr.isPure x = true) : NonInterfering ctx (evalExpr ctx x) e := by
  intro m a m' h
  have : m' = m := (evalExpr_memInvariant ctx x hx).out m _ m' h
  rw [this]

#print axioms evalArgs_pure_pointwise
#print axioms evalArgs_orderIndependent
#print axioms evalArgs_pair_swap
#print axioms evalArgs_pair_oneEffect

#print axioms evalExpr_memInvariant
#print axioms evalLValue_memInvariant
#print axioms evalArgs_memInvariant

end LeanModels.C.C23
