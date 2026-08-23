import LeanModels.C.C23.Expr

/-!
# §6.8 Statements and blocks — M2 inch 4

C23 (N3220) §6.8. Citations follow `docs/c23-spec-mirror.md`; refusals
name their Annex J.2 index.

## Fuel arrives HERE, and the census is why

`Expr.lean` is fuel-free and says so at length. Statements are not.
Measured on the shipped corpus:

| | |
| --- | ---: |
| loops (`for` 50, `do` 29, `while` 5) | **84** |
| …containing a call | 64 |
| **…containing NO call at all** | **20** |

**It is the loop, not the call, that forces fuel** — those 20 need it
just the same — which is what corrected the inch-3 draft's "fuel arrives
at inch 5". `execStmt` therefore takes a fuel argument and recurses on it
at exactly ONE place: the loop step. Every other statement recurses
structurally on `Stmt`, so the fuel-free reasoning of inch 3 keeps
working underneath.

The `∃ n, ∀ fuel ≥ n, … = .ok …` threshold form
(`docs/c-semantics-design.md` §4.2) is assembled AROUND `execStmt`.
`fuelMono` — that more fuel never changes a decided answer — is stated
and proved below, because it is the lemma every later threshold argument
rests on.

## TIMEOUT is not a refusal, so it does not live in `Except`

`docs/c23-goal.md` §3: *"TIMEOUT — fuel exhausted. The only exhaustion
outcome; never conflated with REFUSE."* The Python tier's `Run` agrees
structurally: `.ok` and `.exn` carry state, **`.timeout` carries none**,
because a timeout is not an observation of anything.

So the stack gains a base:

```
ExecM α := SemMWith Mem Refusal CDetail Mem α
        = ExceptT Refusal (StateT Mem (Except (Loud CDetail Mem))) α
```

where Core's `Loud` carries fuel exhaustion and the out-of-tier frontier,
and nothing else. A timeout discards
the memory, correctly — there is no world to report.

## WHERE REFUSAL LIVES — RULED, at `docs/family-architecture.md` §3.4

This file first argued that `unsupported` should ride in `ExceptT`
(state-carrying), against Python's `Run` and the ES lane's `Halt`, so an
inch-6 REFUSE row could say what had happened by the time the model
declined.

**The ruling went the other way, and this lane's own census is part of
why.** Putting a refusal in `ExceptT` makes it catchable in principle,
and the implicit defence was that nothing in C intercepts control flow.
The corpus refutes that: **`setjmp` 2, `longjmp` 2, 5 `jmp_buf`
objects** — and signal handlers in the language at large. Inside `ρ`,
"no catch reaches a refusal" is a per-language, per-construct proof
obligation; uncatchability belongs to the definition.

So `unsupported` lives in Core's `Loud` base, and the diagnostic need
is met the better way: **`Loud.unsupported` carries a structured payload
— the cause, plus an OPTIONAL memory snapshot captured AT the refusal
site.** §3.4's existing law pays for it, because every refusal already
routes through a NAMED primitive with its own `@[spec]` lemma, and that
primitive performs the `get` itself (`refuseUnsupported`), so no call
site can forget to.

**Two guards, both structural rather than advisory**: the snapshot is
optional, and it is NEVER an observable — `Halt`'s `BEq` ignores it, and
`Outcome`, which is what a scoreboard compares, has nowhere to put a
`Mem` at all.

`Halt` carrying `timeout` with no state was already aligned and the
ruling confirms it on the merits: state at fuel exhaustion would invite
treating a TIMEOUT as an observation.
-/

namespace LeanModels.C.C23

open LeanModels.C (CType Expr Stmt Decl)

/-! ## The monad

`Loud` and the stack are `Core`'s now (`LeanModels/Core/Outcome.lean`),
so statements and expressions run in the SAME stack — `ExecM` is `EvalM`.
That is not a coincidence to tidy away: it is what the ruling bought. An
expression cannot time out (inch 3 is fuel-free) and a statement can, but
neither can catch a refusal, so one type serves both. -/

/-- The statement evaluator's monad — the same stack expressions use. -/
abbrev ExecM (α : Type) := EvalM α

/-- Run a statement against a starting memory. -/
def ExecM.run (m : Mem) (x : ExecM α) :
    Except (Loud CDetail Mem) (Except Refusal α × Mem) :=
  EvalM.run m x

/-- The verdict, in `docs/c23-goal.md` §3's vocabulary. -/
def ExecM.verdict (m : Mem) (x : ExecM α) : Outcome α := EvalM.verdict m x

/-- Fuel exhaustion, as a named primitive — never a bare `throw`, and not
a `Refusal` at all. Carries no state: a timeout is not an observation. -/
def exhausted : ExecM α := fun _ => .error .timeout

/-! ## §6.8.7 — how a statement can finish

A C statement does not simply complete: it can leave its block in five
ways, and the enclosing construct decides what each one means. -/

/-- The completion of a statement (§6.8.7). -/
inductive Flow where
  /-- Fell off the end. -/
  | normal
  /-- §6.8.7.3 `break` — 8 sites. -/
  | brk
  /-- §6.8.7.2 `continue` — 6 sites. -/
  | cont
  /-- §6.8.7.4 `return`, with a value at 98 of its 103 sites. -/
  | ret (value : Option CVal)
  /-- §6.8.7.1 `goto` — 7 sites reaching exactly 3 labels, every one a
  FORWARD jump within the same function. A `Flow.goto` propagating
  outward to a labelled statement serves that shape; a general `goto`
  needs a CFG, and the census says this corpus does not have one. -/
  | goto (label : String)
deriving Repr, Inhabited, BEq

/-- Does this completion escape the enclosing block? -/
def Flow.escapes : Flow → Bool
  | .normal => false
  | _ => true

/-! ## Reaching inch 3

`ExecM` IS `EvalM`, so there is no lift — the ruling that put `Halt`
underneath both is what removed it. `liftEval` remains as a name, because
naming the boundary is worth more than saving a line: it marks every
place a statement reaches into the expression layer. -/

/-- Reach into the expression evaluator. The identity, deliberately. -/
@[inline] def liftEval (x : EvalM α) : ExecM α := x

/-- Evaluate an expression for its value. -/
def evalE (ctx : Ctx) (e : Expr) : ExecM CVal := liftEval (evalExpr ctx e)

/-- Evaluate an expression for its truth (§6.8.5, §6.8.6: a controlling
expression is compared unequal to 0). -/
def evalCond (ctx : Ctx) (e : Expr) : ExecM Bool :=
  liftEval (do let v ← evalExpr ctx e; truthy v)

/-! ## §6.7.11 — initialization, and the rule that fires on NOTHING

**Measured, on all 75 `InitListExpr` nodes in the corpus: every one is
FULL.** Not one array initializer is shorter than its extent and not one
structure initializer omits a member. So §6.7.11p10's rule — *the
unmentioned members are initialized as objects with static storage
duration*, i.e. to zero — **fires on zero corpus sites.**

That is exactly the condition under which the memory model installed
effective types (§2.5): a rule is cheap to install correctly while
nothing exercises it and expensive to retrofit afterwards, and **no
instrument in this project would otherwise notice it was missing.** So it
is implemented, and gated on a SYNTHETIC partial initializer, because the
corpus cannot exercise it and a rule nobody ran is a rule nobody checked.

**Zero-initialization is TYPE-DIRECTED, not a memset.** §6.7.11p10 says
the unmentioned members are initialized *as if by `= 0`*, and for a
pointer member that is a NULL POINTER, not all-bits-zero. Writing zero
bytes over a pointer member would make it read back as an integer and
`loadPtr` would refuse it — a wrong answer that looks like a right one.
So the recursion below dispatches on the member's type. -/

mutual

/-- §6.7.11p10 — initialize an object to zero, as if it had static
storage duration. Type-directed: see the section note. -/
def zeroInit : Nat → Ctx → Ptr → CType → ExecM Unit
  | 0, _, _, _ => exhausted
  | fuel + 1, ctx, p, ty =>
    match intTyOf? ty with
    -- an integer member: the value zero at its own width
    | some t => liftEval (writeMem (fun m => Mem.storeInt m p t 0))
    | none =>
      if isPtrType ty then
        -- §6.3.2.3p3: `= 0` on a pointer is a NULL POINTER, not zero bytes
        liftEval (writeMem (fun m => Mem.storePtr m p Ptr.null))
      else
        match ctx.layout.elem ty with
        | some (et, n) =>
            match ctx.layout.size et with
            | some esz => zeroElems fuel ctx p et esz n 0
            | none => refuseUnsupported s!"no size for element type '{et}'"
        | none =>
          match ctx.layout.members ty with
          | some ms => zeroMembers fuel ctx p ty ms
          | none => refuseUnsupported s!"cannot zero-initialize '{ty}'"

/-- Zero the elements of an array, from index `i` up. -/
def zeroElems : Nat → Ctx → Ptr → CType → Nat → Nat → Nat → ExecM Unit
  | 0, _, _, _, _, _, _ => exhausted
  | fuel + 1, ctx, p, et, esz, n, i =>
    if i ≥ n then pure ()
    else do
      zeroInit fuel ctx (Mem.member p (i * esz)) et
      zeroElems fuel ctx p et esz n (i + 1)

/-- Zero the members of a structure, in declaration order. -/
def zeroMembers : Nat → Ctx → Ptr → CType → List (String × CType) → ExecM Unit
  | 0, _, _, _, _ => exhausted
  | _, _, _, _, [] => pure ()
  | fuel + 1, ctx, p, ty, (nm, mty) :: rest => do
      match ctx.layout.fieldOff ty nm with
      | some off => zeroInit fuel ctx (Mem.member p off) mty
      | none => refuseUnsupported s!"no offset for member '{nm}'"
      zeroMembers fuel ctx p ty rest

end

/-! ### The initializer proper -/

mutual

/-- §6.7.11 — initialize the object at `p`, of type `ty`, from `e`.

A scalar initializer is an assignment (§6.7.11p11). A brace-enclosed list
initializes an aggregate member by member (p9), **in declaration order**,
and every member the list does not reach is zeroed (p10). -/
def initObject : Nat → Ctx → Ptr → CType → Expr → ExecM Unit
  | 0, _, _, _, _ => exhausted
  | fuel + 1, ctx, p, ty, e =>
    match e with
    | .initList inits _ _ =>
        match ctx.layout.elem ty with
        -- an ARRAY: elements at i * sizeof(elem), then §6.7.11p10 on the tail
        | some (et, n) =>
            match ctx.layout.size et with
            | some esz => initElems fuel ctx p et esz n 0 inits
            | none => refuseUnsupported s!"no size for element type '{et}'"
        | none =>
          match ctx.layout.members ty with
          -- a STRUCTURE: members in declaration order, then p10 on the rest
          | some ms => initMembers fuel ctx p ty ms inits
          | none => refuseUnsupported s!"cannot initialize aggregate '{ty}'"
    -- §6.7.11p11 — a scalar initializer is a single expression.
    | _ => do
        let v ← evalE ctx e
        liftEval (storeAt p ty v)

/-- Array elements, then zero-fill (§6.7.11p10). -/
def initElems : Nat → Ctx → Ptr → CType → Nat → Nat → Nat → List Expr → ExecM Unit
  | 0, _, _, _, _, _, _, _ => exhausted
  | fuel + 1, ctx, p, et, esz, n, i, es =>
    match es with
    -- the list ran out: every remaining element is zeroed
    | [] => zeroElems fuel ctx p et esz n i
    | e :: rest =>
        if i ≥ n then
          -- §6.7.11p2 is a CONSTRAINT: more initializers than elements.
          refuseUnsupported "more initializers than array elements"
        else do
          initObject fuel ctx (Mem.member p (i * esz)) et e
          initElems fuel ctx p et esz n (i + 1) rest

/-- Structure members in declaration order, then zero-fill. -/
def initMembers : Nat → Ctx → Ptr → CType → List (String × CType) → List Expr → ExecM Unit
  | 0, _, _, _, _, _ => exhausted
  | fuel + 1, ctx, p, ty, ms, es =>
    match ms, es with
    | [], [] => pure ()
    | [], _ :: _ => refuseUnsupported "more initializers than structure members"
    -- the list ran out: §6.7.11p10 zeroes every member it did not reach
    | rest, [] => zeroMembers fuel ctx p ty rest
    | (nm, mty) :: mrest, e :: erest => do
        match ctx.layout.fieldOff ty nm with
        | some off => initObject fuel ctx (Mem.member p off) mty e
        | none => refuseUnsupported s!"no offset for member '{nm}'"
        initMembers fuel ctx p ty mrest erest

end

/-! ## §6.8.7.1 — `goto`, and why a label search is enough

Measured: the corpus's **7 `goto`s reach exactly 3 labels**
(`after_moves` x3, `out` x3, `reset_ok` x1), and **every one is a FORWARD
jump to a label in the same function at the same or an enclosing block
level.** That is precisely the shape a block can serve by scanning the
statements it has not run yet; a backward or into-a-block jump would need
a control-flow graph, and this corpus has none. A jump whose label is not
found propagates outward, and reaching the top of a function unmatched is
a refusal rather than a silent fall-through. -/

/-- The statements from `label` onward, if it is among these. -/
def findLabel (name : String) : List Stmt → Option (List Stmt)
  | [] => none
  | s :: rest =>
      match s with
      | .label n body sp => if n == name then some (.label n body sp :: rest)
                            else findLabel name rest
      | _ => findLabel name rest

/-! ## §6.8 — the statement evaluator

Fuel decreases on EVERY recursive call, not only at the loop step. That
is stricter than §4.6.1 needs — a block is not an iteration — but it
makes the recursion structural on `Nat` with no measure to justify, and
fuel is a bound on total work rather than on iterations alone. The
`∃ n, ∀ fuel ≥ n` threshold form is unaffected: it quantifies over fuel
from outside. -/

mutual

/-- §6.8 — execute one statement, yielding how it completed. -/
def execStmt : Nat → Ctx → Stmt → ExecM Flow
  | 0, _, _ => exhausted
  | fuel + 1, ctx, s => match s with
    -- §6.8.3 — a block. Declarations inside it extend the environment,
    -- which is why the block threads a context rather than reading one.
    | .compound body _ => execBlock fuel ctx body
    -- §6.8.4 — an expression statement: evaluated for its EFFECTS, value
    -- discarded. 297 sites, the largest statement class in the corpus.
    | .expr e _ => do let _ ← evalE ctx e; pure .normal
    -- §6.8.5.1 — `if`. Measured: only 51 of 253 carry an `else`, so the
    -- else-less arm is the common path and is written first.
    | .ifS c t none _ => do
        if (← evalCond ctx c) then execStmt fuel ctx t else pure .normal
    | .ifS c t (some e) _ => do
        if (← evalCond ctx c) then execStmt fuel ctx t else execStmt fuel ctx e
    -- §6.8.7.4 — `return`, with a value at 98 of 103 sites.
    | .ret none _ => pure (.ret none)
    | .ret (some e) _ => do let v ← evalE ctx e; pure (.ret (some v))
    | .breakS _ => pure .brk              -- §6.8.7.3, 8 sites
    | .continueS _ => pure .cont          -- §6.8.7.2, 6 sites
    | .goto l _ => pure (.goto l)         -- §6.8.7.1, 7 sites
    -- A labelled statement runs its body; the LABEL is found by the
    -- enclosing block (`findLabel`), not by the statement itself.
    | .label _ body _ => execStmt fuel ctx body
    -- §6.8.6.2 — `while`. 5 sites.
    | .whileS c body _ => execLoop fuel ctx (some c) none body false
    -- §6.8.6.3 — `do … while`: the body runs BEFORE the first test. 29 sites.
    | .doS body c _ => execLoop fuel ctx (some c) none body true
    -- §6.8.6.4 — `for`. 50 sites; 48 carry `init`, 49 carry `cond`, 50 carry
    -- `inc` — so THREE sites omit a clause (two omit `init`, one omits
    -- `cond`) and the omitted-clause arms are
    -- three sites rather than a third of them. An omitted `cond` is TRUE.
    | .forS init c inc body _ => do
        match init with
        | some i => do
            let f ← execStmt fuel ctx i
            match f with
            | .normal => execLoop fuel ctx c inc body false
            | other => pure other
        | none => execLoop fuel ctx c inc body false
    -- A bare declaration reaching here is one the block did not thread;
    -- `execBlock` handles them, so this is unreachable in practice and
    -- refuses rather than silently doing nothing.
    | .decl _ _ => refuseUnsupported "declaration outside a block"
    | .unsupported k _ _ => refuseUnsupported s!"out of tier: {k}"

/-- Run a block's statements in order, threading the environment that
declarations extend and honouring a forward `goto` into the remainder. -/
def execBlock : Nat → Ctx → List Stmt → ExecM Flow
  | 0, _, _ => exhausted
  | _, _, [] => pure .normal
  | fuel + 1, ctx, s :: rest =>
    match s with
    -- §6.7 — a declaration extends the environment for the REST of the
    -- block. C23 §6.7p5 sequences declarators left to right, each fully
    -- before the next, which `declare` follows.
    | .decl ds _ => do
        let ctx' ← declare fuel ctx ds
        execBlock fuel ctx' rest
    | _ => do
      let f ← execStmt fuel ctx s
      match f with
      | .normal => execBlock fuel ctx rest
      | .goto l =>
          -- §6.8.7.1: a forward jump lands on a label later in THIS block,
          -- or propagates outward to an enclosing one.
          match findLabel l rest with
          | some tail => execBlock fuel ctx tail
          | none => pure (.goto l)
      | other => pure other

/-- One loop, with fuel decreasing per ITERATION.

`post` is `do … while`: the body runs before the first test. `inc` is
`for`'s third clause, evaluated after the body and before the next test —
and, per §6.8.6.4p2, **also after a `continue`**, which is the detail a
model gets wrong by treating `continue` as `break`. -/
def execLoop : Nat → Ctx → Option Expr → Option Expr → Stmt → Bool → ExecM Flow
  | 0, _, _, _, _, _ => exhausted
  | fuel + 1, ctx, cond, inc, body, post => do
      -- an omitted controlling expression is TRUE (§6.8.6.4p2)
      let go ← if post then pure true
               else match cond with
                    | some c => evalCond ctx c
                    | none => pure true
      if !go then pure .normal
      else do
        let f ← execStmt fuel ctx body
        match f with
        | .brk => pure .normal            -- §6.8.7.3: break ENDS the loop
        | .ret v => pure (.ret v)
        | .goto l => pure (.goto l)
        | .normal | .cont => do
            -- §6.8.6.4p2: `continue` still runs the increment.
            match inc with
            | some e => do let _ ← evalE ctx e; pure ()
            | none => pure ()
            execLoop fuel ctx cond inc body false

/-- §6.7 — create the objects a declaration introduces and bind their
names, left to right.

Measured: 273 of 321 `VarDecl`s carry an initializer, and **75
`InitListExpr` nodes** appear in the corpus (35 top-level, 40 nested).
Both shapes go through `initObject` (§6.7.11). -/
def declare : Nat → Ctx → List Decl → ExecM Ctx
  | 0, _, _ => exhausted
  | _, ctx, [] => pure ctx
  | fuel + 1, ctx, d :: ds =>
    match d with
    | .var name ty _ init _ => do
        match ctx.layout.size ty with
        | none => refuseUnsupported s!"no layout for declared type '{ty}'"
        | some sz => do
            -- §6.2.4p6: an automatic object lives from block entry, with
            -- an INDETERMINATE representation until something writes it.
            let m ← get
            let (m', o) := m.alloc .automatic sz (some ty)
            set m'
            let ctx' := { ctx with env := (name, o) :: ctx.env }
            match init with
            | none => declare fuel ctx' ds
            | some e => do
                -- §6.7.11 — scalar or aggregate, one entry point.
                initObject fuel ctx' (Ptr.toObject o) ty e
                declare fuel ctx' ds
    | _ => refuseUnsupported "non-object declaration in a block"

end

/-! ## §6.5.3.3 — function calls: inch 5

**The call graph is almost entirely acyclic, and the census is the
decision-relevant fact.** Of 58 defined functions, exactly **one is
directly self-recursive** (`bound`, the search) and there is **one mutual
cycle of size two** (`bound` ↔ `score_move`). Everything else is a DAG.

So fuel, which arrived at inch 4 for loops, arrives here for a call graph
whose cyclic part is two functions wide. It is still needed — a model
cannot know the graph is acyclic without proving it — but the measurement
says the fuel-consuming surface is small, and it names exactly which
functions a termination argument would have to be about.

Where the 320 call sites go:

| | sites |
| --- | ---: |
| to one of the 58 DEFINED functions | **155** |
| to one of the 27 libc externals — cause `libc` | **146** |
| INDIRECT, every one through `movecb` | **19** |

Nearly half of all calls leave the tier, and they refuse as `libc` — the
cause that retires by widening the slice, never pooled with the others. -/

/-- The functions a call can reach, with the layout and enumeration
constants they need. -/
structure Program where
  fns : List LeanModels.C.FunctionDefn
  layout : Layout := Layout.unknown
  enums : List (String × Int) := []

def Program.find? (p : Program) (name : String) : Option LeanModels.C.FunctionDefn :=
  p.fns.find? (·.name == name)

/-- §6.5.3.3p4 — evaluate the arguments, LEFT TO RIGHT.

**Currently unreachable**: the handler's reverted signature gives it no
evaluator to pass here. Kept because it is the canonical-order half of
Thomas's `∀ order` ruling and the shape the repair will re-attach to.

**Left-to-right is the CANONICAL order, not the claim.** §6.5.3.3p10
leaves the order indeterminately sequenced, and Thomas's ruling makes
correctness a `∀ order` property; this function is how a witness is
extracted, and the obligation is discharged per-site over the 7 sites the
census found (`docs/c23-spec-mirror.md` §5.3). Structural on the list, so
no fuel enters here. -/
def evalArgsLR (ev : LeanModels.C.Expr → EvalM CVal) : List LeanModels.C.Expr → ExecM (List CVal)
  | [] => pure []
  | e :: es => do
      let v ← ev e
      let vs ← evalArgsLR ev es
      pure (v :: vs)

/-- §6.5.3.3p4 / §6.9.2p7 — give each parameter its own automatic object
and store the argument into it.

A parameter IS an object (§6.9.2p7: "the parameters are declared as if by
declaration in the compound statement"), which is why 1 of the corpus's
31 `&`-of-automatic sites takes the address of one. Measured parameter
counts: 0-9, and 39 of 58 functions take two or fewer. -/
def bindParams (lay : Layout) : Ctx → List LeanModels.C.Decl → List CVal → ExecM Ctx
  | ctx, [], [] => pure ctx
  | _, [], _ :: _ => refuseUnsupported "more arguments than parameters"
  | _, _ :: _, [] => refuseUnsupported "fewer arguments than parameters"
  | ctx, d :: ps, v :: vs =>
    match d with
    | .param n ty _ =>
        match lay.size ty with
        | none => refuseUnsupported s!"no layout for parameter type '{ty}'"
        | some sz => do
            let m ← get
            let (m', o) := m.alloc .automatic sz (some ty)
            set m'
            liftEval (storeAt (Ptr.toObject o) ty v)
            bindParams lay { ctx with env := (n, o) :: ctx.env } ps vs
    | _ => refuseUnsupported "non-parameter in a parameter list"

/-- §6.5.3.3 — call a defined function with already-evaluated arguments.

The handler the callee's frame carries is built HERE, closing over the
decremented fuel: that is the whole recursion, and it is why fuel is a
parameter of this function rather than of `evalExpr`.

A `void` function answers `.undef`, not a fabricated zero — the value of
a `void` call may not be used (§6.5.3.3p3), and `.undef` is the value
every consumer already refuses. Returning `0` would have been a number
somebody could read. -/
def callFn : Nat → Program → LeanModels.C.FunctionDefn → List CVal → ExecM CVal
  | 0, _, _, _ => exhausted
  | fuel + 1, prog, f, args =>
    match f.body with
    | none => refuseUnsupported s!"'{f.name}' is a prototype, not a definition"
    | some body => do
        -- The callee's own call handler: one fuel less, so the recursion
        -- terminates on the fuel and on nothing else.
        let handler : CallHandler := fun callee _ =>
          let nm := calleeNameOf callee
          if nm == "<indirect>" then
            -- 19 sites, every one through `movecb`. The callback protocol
            -- needs a function POINTER value, which the value model does
            -- not carry yet — named, not silently mishandled.
            refuseUnsupported "indirect call through a function pointer (movecb)"
          else
            match prog.find? nm with
            -- One of the 27 externals. Classifiable WITHOUT evaluating the
            -- arguments, which is why this arm survives the handler's
            -- reverted signature: cause `libc`, which retires by widening
            -- the slice and never pools with the other two.
            | none => throw (.libc nm)
            -- A NESTED call to a defined function needs its arguments
            -- evaluated in the CALLER's scope, and the handler no longer
            -- receives a way to do that — see `CallHandler`'s note. This is
            -- inch 5's open problem, refused by name rather than guessed.
            | some _ => refuseUnsupported
                s!"nested call to '{nm}' — argument evaluation is inch 5's open problem"
        let ctx0 : Ctx :=
          { env := [], enums := prog.enums, layout := prog.layout, call := handler }
        let ctx ← bindParams prog.layout ctx0 f.params args
        let flow ← execStmt fuel ctx body
        match flow with
        | .ret (some v) => pure v
        | .ret none => pure .undef
        -- §5.1.2.3.4: falling off the end of a non-void function is
        -- undefined ONLY if the caller uses the value; `main` is the
        -- exception and returns 0. Neither is decided here.
        | .normal => pure .undef
        | _ => refuseUnsupported "break, continue or goto escaped a function body"

/-- Call by NAME — the entry point a scoreboard uses. -/
def callByName (fuel : Nat) (prog : Program) (name : String) (args : List CVal) :
    ExecM CVal :=
  match prog.find? name with
  | some f => callFn fuel prog f args
  | none => refuseUnsupported s!"no definition for '{name}'"

/-! ## `fuelMono` — still an obligation, and now with a known technique

The lemma every `∃ n, ∀ fuel ≥ n` argument rests on
(`docs/c-semantics-design.md` §4.2): more fuel never changes a decided
answer.

**NOT PROVED HERE, and the reason is worth recording rather than
apologising for.**

*The technique is no longer open.* `LeanModels/Sv/Obs.lean` already
solves this exact problem: a flat approximation order `⊑` with `timeout`
at the bottom, `fuelMono` stated as ONE CONJUNCTION over the whole mutual
block, proved by induction on fuel with a `le_bind` congruence doing the
work at each operator. **96 lines for four functions.** This lane should
LIFT that machinery, not write a second copy of it — the `⊑` order and
its bind congruence are generic in the result type, and a second
hand-rolled monotonicity order is precisely the duplication
`docs/family-architecture.md` §9.2 exists to stop.

*What makes it more than a transcription here.* This mutual block is TEN
functions, not four — `execStmt`, `execBlock`, `execLoop`, `declare`,
`initObject`, `initElems`, `initMembers`, `zeroInit`, `zeroElems`,
`zeroMembers` — so the conjunction has ten conjuncts. And where SV's
functions return a result directly, these return a MONADIC value, so
monotonicity is pointwise in the memory: `∀ m, run m (f fuel …) ⊑ run m
(f fuel' …)`. Both are mechanical against the template; neither is free.

*Why it was not attempted in this session, specifically.* Proof
iteration needs many short Lean runs, and under build-lock Amendment 11
every one of them needs a tenure — which cost this lane **88 minutes** of
FIFO queueing on its last landing. A 300-line proof developed at one
compile per tenure is not a session's work; it is a week's. **That is the
lock's real cost on PROOF work as distinct from build verification**, and
it is a different shape of problem from the starvation the ticket queue
fixed. Reported rather than worked around.

So the obligation is stated as a `Prop` below — visible, named, and
impossible to mistake for a theorem. -/

/-- More fuel never turns a decided answer into a different one.

`Loud.timeout` is the bottom: a run that exhausted its fuel may become
anything at higher fuel, and a run that DECIDED keeps its exact answer,
memory included. -/
def FuelMono : Prop :=
  ∀ (fuel : Nat) (ctx : Ctx) (s : Stmt) (m : Mem) (r : Except Refusal Flow) (m' : Mem),
    ExecM.run m (execStmt fuel ctx s) = .ok (r, m') →
    ∀ fuel' ≥ fuel, ExecM.run m (execStmt fuel' ctx s) = .ok (r, m')

end LeanModels.C.C23
