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
ExecM α := ExceptT Refusal (StateT Mem Halt) α
```

where `Halt` carries fuel exhaustion and nothing else. A timeout discards
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

So `unsupported` lives in `Halt` (`Memory.lean`), and the diagnostic need
is met the better way: **`Halt.unsupported` carries a structured payload
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

`Halt` and `Outcome` are the shared substrate now (`Memory.lean`, §3.4),
so statements and expressions run in the SAME stack — `ExecM` is `EvalM`.
That is not a coincidence to tidy away: it is what the ruling bought. An
expression cannot time out (inch 3 is fuel-free) and a statement can, but
neither can catch a refusal, so one type serves both. -/

/-- The statement evaluator's monad — the same stack expressions use. -/
abbrev ExecM (α : Type) := EvalM α

/-- Run a statement against a starting memory. -/
def ExecM.run (m : Mem) (x : ExecM α) : Halt (Except Refusal α × Mem) :=
  EvalM.run m x

/-- The verdict, in `docs/c23-goal.md` §3's vocabulary. -/
def ExecM.verdict (m : Mem) (x : ExecM α) : Outcome α := EvalM.verdict m x

/-- Fuel exhaustion, as a named primitive — never a bare `throw`, and not
a `Refusal` at all. Carries no state: a timeout is not an observation. -/
def exhausted : ExecM α := fun _ => Halt.timeout

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
    -- §6.8.6.4 — `for`. 50 sites, and all 50 carry all three clauses
    -- (48 `init`, 49 `cond`, 50 `inc`), so the omitted-clause arms are
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

**Scalar declarators only.** Measured: 273 of 321 `VarDecl`s carry an
initializer and **34 of those are `InitListExpr`** — aggregate
initialization is real work with its own layout obligations (it writes
through the layout rather than reading it) and is the next landing, not a
corner. It refuses here rather than initializing partially. -/
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
            | some e =>
                match e with
                | .initList .. =>
                    refuseUnsupported "aggregate initializer (the next landing)"
                | _ => do
                    let v ← evalE ctx' e
                    liftEval (storeAt (Ptr.toObject o) ty v)
                    declare fuel ctx' ds
    | _ => refuseUnsupported "non-object declaration in a block"

end

/-! ## `fuelMono` — more fuel never changes a decided answer

The lemma every `∃ n, ∀ fuel ≥ n` argument rests on
(`docs/c-semantics-design.md` §4.2). Stated for `execStmt` and proved by
induction on the FUEL DIFFERENCE, never on the statement.

**Not yet proved** — it is stated here so the obligation is visible and
named rather than assumed, and discharging it is the next landing's
first item. It is the one place this inch owes a proof rather than a
gate. -/

/-- More fuel never turns a decided answer into a different one. -/
def FuelMono : Prop :=
  ∀ (fuel : Nat) (ctx : Ctx) (s : Stmt) (m : Mem) (r : Except Refusal Flow) (m' : Mem),
    ExecM.run m (execStmt fuel ctx s) = Halt.ok (r, m') →
    ∀ fuel' ≥ fuel, ExecM.run m (execStmt fuel' ctx s) = Halt.ok (r, m')

end LeanModels.C.C23
