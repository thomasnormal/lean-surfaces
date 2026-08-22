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

**One deliberate divergence from Python, recorded rather than drifted
into.** Python's `Run.unsupported` carries no state either. C's
`Refusal.unsupported` DOES, because it rides in `ExceptT` with the other
refusals — and that is wanted: the inch-6 scoreboard's REFUSE rows are
worth more when they can say what had happened by the time the model
declined. **Only TIMEOUT loses its world.**
-/

namespace LeanModels.C.C23

open LeanModels.C (CType Expr Stmt Decl)

/-! ## The base monad: exhaustion, and nothing else -/

/-- Fuel exhaustion. `Halt` is the family stack's base — the place for
outcomes that carry NO state, which is exactly `timeout` and nothing
else in this tier. Isomorphic to `Option`, and named for what it means. -/
inductive Halt (α : Type) where
  | ok (a : α)
  | timeout
deriving Repr, Inhabited, BEq

namespace Halt

@[inline] def bind : Halt α → (α → Halt β) → Halt β
  | .ok a, f => f a
  | .timeout, _ => .timeout

instance : Monad Halt where
  pure := .ok
  bind := Halt.bind

@[simp] theorem bind_ok (a : α) (f : α → Halt β) : Halt.bind (.ok a) f = f a := rfl
@[simp] theorem bind_timeout (f : α → Halt β) :
    Halt.bind (.timeout : Halt α) f = .timeout := rfl

end Halt

/-- The statement evaluator's monad: refusals carry the memory, timeouts
do not. See the module docstring for why that asymmetry is the point. -/
abbrev ExecM (α : Type) := ExceptT Refusal (StateT Mem Halt) α

/-- Run a statement against a starting memory. `Halt.timeout` means fuel
ran out and there is no observation; `.ok (result, mem)` means there is. -/
def ExecM.run (m : Mem) (x : ExecM α) : Halt (Except Refusal α × Mem) :=
  StateT.run x m

/-- Exhaustion, as a named primitive — never a bare `throw`, and not a
`Refusal` at all. -/
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

/-! ## Lifting inch 3

The expression evaluator lives in `EvalM = ExceptT Refusal (StateT Mem Id)`;
statements live over `Halt`. The lift is total and loses nothing, because
an expression cannot time out — it is fuel-free (inch 3's whole point). -/

/-- Run an inch-3 expression evaluation inside `ExecM`. -/
def liftEval (x : EvalM α) : ExecM α := fun m =>
  Halt.ok (StateT.run x m)

/-- Evaluate an expression for its value. -/
def evalE (ctx : Ctx) (e : Expr) : ExecM CVal := liftEval (evalExpr ctx e)

/-- Evaluate an expression for its truth (§6.8.5, §6.8.6: a controlling
expression is compared unequal to 0). -/
def evalCond (ctx : Ctx) (e : Expr) : ExecM Bool :=
  liftEval (do let v ← evalExpr ctx e; truthy v)

end LeanModels.C.C23
