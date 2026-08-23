import LeanModels.Go.Sem
import LeanModels.Go.SpecAttr

/-!
# THE SEAM — one opening of the monad stack

`docs/family-architecture.md` §3.4 fixes both the shape and the count:
*"one opening of the monad stack is the right number."* This file is that
opening for the Go tier, plus the corollaries that follow from it, tagged
into a single simp set named `go_run`.

## Why this file has to exist at all

`docs/backlog/go.md` §G8 recorded the loop induction as blocked, and named
the blocker precisely: stepping the walker means reducing
`GoM = SemMWith GoWorld Panic SpecRef Unit` applied to a world, and **that
is not `rfl`** — measured, `lookupLocal name w` is not definitionally the
match on `w.locals.find? …`. Every proof step needed a rewrite through
`ExceptT`, `StateT` and `Except`, and the lane had no lemma for it, so
each attempt re-derived the unfolding by hand against a bare `simp`.

The Python lane hit the same wall and answered it with `py_simp` over an
`Obs` spine. **This is the Go analogue, and it is cheaper than Python's
was** for a reason worth recording: Python's `Run` is a DATATYPE, so its
`bind` reduces by cases and it never needed an opener — what it needed
was the approximation-order congruences. `GoM` is a transformer STACK, so
the opener is the thing that was missing, and it is one lemma.

## The division of labour, and §3.4's ruling

> **The ORDER lifts; the CONGRUENCES don't.**

Core supplies the order layer for the whole `SemMWith` stack. The
congruences stay per-tier, because each is about a *different* monad's
`bind` — Python's `Res` carries an `.exn` arm this one does not, so a
lifted congruence would be the thick-trunk mistake. §3.4 enumerates six
shapes: `bind`, `ite`, `tryCatch` from the monad, `zoomIn`/`zoomOut` from
the state zoom, and the `liftRes` analogue. **This file lands the first
and the primitives; the rest arrive when a consumer needs them, which is
the same discipline that kept `fallthrough` out of rung 2.**
-/

namespace LeanModels.Go

variable {α β : Type}

/-! ## §1 THE SEAM

Everything else in this file is a corollary of this one lemma. It says
what running a bind DOES: run the first computation, and then — on the
three outcomes the stack can produce — stop loudly, propagate the panic
with its world, or continue with the value in the world it left. -/

/-- **THE OPENING.** One lemma, and the only place the stack is unfolded
by hand. -/
@[go_run] theorem run_bind (x : GoM α) (f : α → GoM β) (w : GoWorld) :
    (x >>= f) w
      = (match x w with
         | .error h => .error h
         | .ok (.error e, w') => .ok (.error e, w')
         | .ok (.ok a, w') => f a w') := by
  simp [bind, ExceptT.bind, ExceptT.mk, StateT.bind, ExceptT.bindCont]
  cases hx : x w with
  | error h => simp [Except.bind]
  | ok p =>
    obtain ⟨r, w'⟩ := p
    cases r <;> simp [Except.bind, pure, StateT.pure, Except.pure]

/-! ## §2 THE PRIMITIVES

Each is a constant of the tier, so each gets its own row rather than
being re-derived at every call site. These are what make a walker step
reduce: after `run_bind` splits a `do` block, the head is always one of
these. -/

@[go_run] theorem run_pure (a : α) (w : GoWorld) :
    (pure a : GoM α) w = .ok (.ok a, w) := rfl

@[go_run] theorem run_get (w : GoWorld) :
    (get : GoM GoWorld) w = .ok (.ok w, w) := rfl

@[go_run] theorem run_set (w w' : GoWorld) :
    (set w' : GoM PUnit) w = .ok (.ok ⟨⟩, w') := rfl

@[go_run] theorem run_modify (f : GoWorld → GoWorld) (w : GoWorld) :
    (modify f : GoM PUnit) w = .ok (.ok ⟨⟩, f w) := rfl

/-- A refusal is state-DISCARDING and uncatchable — the covenant, as a
reduction rule. -/
@[go_run] theorem run_refuseGo (r : GoRefusal) (π : SpecRef) (m : String)
    (w : GoWorld) :
    (refuseGo r π m : GoM α) w = .error (.unsupported (r.toCore π) m none) := rfl

@[go_run] theorem run_exhausted (w : GoWorld) :
    (LeanModels.exhausted : GoM α) w = .error .timeout := rfl

/-- A panic is state-RETAINING — the ρ channel, and the reason the layer
order is what it is. -/
@[go_run] theorem run_raiseIn (e : Panic) (w : GoWorld) :
    (LeanModels.raiseIn e : GoM α) w = .ok (.error e, w) := rfl

/-! ## §3 THE COROLLARIES

`map` is `pure`-after-`bind`, so it needs no second opening — which is
the point of having exactly one. -/

@[go_run] theorem run_map (g : α → β) (x : GoM α) (w : GoWorld) :
    (g <$> x) w
      = (match x w with
         | .error h => .error h
         | .ok (.error e, w') => .ok (.error e, w')
         | .ok (.ok a, w') => .ok (.ok (g a), w')) := by
  rw [map_eq_pure_bind, run_bind]
  cases hx : x w with
  | error h => rfl
  | ok p => obtain ⟨r, w'⟩ := p; cases r <;> rfl

/-- Sequencing without a value — the `do` block's `let _ ← …` shape. -/
@[go_run] theorem run_seqRight (x : GoM α) (y : GoM β) (w : GoWorld) :
    (x >>= fun _ => y) w
      = (match x w with
         | .error h => .error h
         | .ok (.error e, w') => .ok (.error e, w')
         | .ok (.ok _, w') => y w') := run_bind x _ w

end LeanModels.Go
