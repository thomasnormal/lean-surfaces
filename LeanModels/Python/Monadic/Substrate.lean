/-
**The monadic rebuild's SUBSTRATE** — `docs/python-monadic-rebuild.md` is its plan.

This is the family substrate of `docs/family-architecture.md` §3.4, instantiated
for Python: `SemM W ρ = ExceptT ρ (StateT W (Except Halt))`, the layer order the
`mvcgen` pilot CORRECTED by `rfl` (the failure barrel must see the world, because
`Run`'s `.exn` retains state and `PyPost.err` is state-aware).

**THE BOUNDARY.** `LeanModels/Python/Monadic/` is a PRESENTATION sibling, not a
VERSION sibling: it claims the same edition as the trunk (CPython 3.9), the same
oracle and the same corpus, and it re-presents the trunk's semantics in
do-notation. It is NOT an edition token and must never be read as one — when the
Python lane earns `LeanModels/Python/Py39/` under §1.1, that directory is an
orthogonal axis to this one. Nothing here is imported by `LeanModels/Python.lean`
while the old interpreter is authoritative.

**WHAT IS SHARED, AND IT IS THE MAXIMAL TRUNK.** Every pure worker of
`LeanModels/Python/Semantics.lean` — `evalBinOp`, `indexValH`, `sliceVal`,
`truthyH`, `assignToH`, `strCallPlan`, `attrCallPlan`, the string workers, the
render workers — is REUSED verbatim. The rebuild re-presents the interpreter's
CONTROL, not its arithmetic; a second copy of `evalBinOp` would be a second thing
to keep true.

Zero `sorry`. Zero `native_decide`. `#print axioms` on every theorem.
-/
import LeanModels.Python.Semantics

open LeanModels LeanModels.Python

namespace LeanModels.Python.Monadic

/-- `Run`'s two state-DISCARDING outcomes, as a NAMED type.

Deliberately an `inductive` and not the pilot's `Unit ⊕ String`: a refusal is a
first-class notion in this family (§0.1's loudness doctrine), and the sum spells
the two arms as anonymous injections at every use site. A Core candidate once a
second tier wants it — recorded in the plan, not moved here. -/
inductive Halt where
  /-- Fuel exhaustion, and ONLY fuel exhaustion. -/
  | timeout
  /-- The loud, fuel-INDEPENDENT semantic frontier. -/
  | unsupported (msg : String)
deriving Repr, Inhabited, BEq, DecidableEq

/-- **The substrate.** `ExceptT ρ (StateT W Halt)` — `family-architecture.md`
§3.4 as corrected by the pilot. `StateT` OUTSIDE `ExceptT` discards the state on
a raise and cannot state this tier's own error postcondition; the order below is
the one whose failure barrel has type `ρ → W → ULift Prop`. -/
abbrev SemM (W : Type) (ρ : Type) := ExceptT ρ (StateT W (Except Halt))

/-- Python's instantiation: the refusal payload is `PyErr`. -/
abbrev PyM (σ : Type) := SemM σ PyErr

/-- Statement/expression execution transforms a `FrameState`. -/
abbrev SemF := PyM FrameState

/-- A nested call passes only the `World` through. -/
abbrev SemW := PyM World

/-! ## §1 THE ISOMORPHISM — `Run σ` IS this stack, proved both ways -/

/-- `Run σ α` as a `PyM σ α`. -/
def ofRun (r : σ → Run σ α) : PyM σ α := fun s =>
  match r s with
  | .ok s' a       => .ok (.ok a, s')
  | .exn s' e      => .ok (.error e, s')
  | .timeout       => .error .timeout
  | .unsupported m => .error (.unsupported m)

/-- A `PyM σ α` as a `Run σ α`. This is the RUNNER's boundary: the monadic
interpreter is handed to `Main.lean` through it, so the two interpreters are
compared as the SAME type by the same harnesses. -/
def toRun (x : PyM σ α) : σ → Run σ α := fun s =>
  match x s with
  | .ok (.ok a, s')         => .ok s' a
  | .ok (.error e, s')      => .exn s' e
  | .error .timeout         => .timeout
  | .error (.unsupported m) => .unsupported m

theorem toRun_ofRun (r : σ → Run σ α) : toRun (ofRun r) = r := by
  funext s; simp only [toRun, ofRun]; cases r s <;> rfl

theorem ofRun_toRun (x : PyM σ α) : ofRun (toRun x) = x := by
  funext s
  rcases h : x s with l | ⟨v, s'⟩
  · rcases l with _ | m <;> simp [toRun, ofRun, h]
  · rcases v with a | e <;> simp [toRun, ofRun, h]

/-! ## §2 THE NAMED REFUSAL PRIMITIVES

**Never a bare polymorphic `throw` in interpreter code.** The pilot found a real
Std bug behind that rule (`Spec.throw_Except` carries binders its conclusion does
not determine, so a bare `throw` leaves universe-level metavariables and the
declaration is REJECTED), and the rule is what this family wants anyway. Every
failure below is a named primitive with its own `@[spec]` lemma in `Spec.lean`. -/

/-- The loud, fuel-independent semantic frontier. -/
def refuse (msg : String) : PyM σ α := fun _ => .error (.unsupported msg)

/-- Fuel exhaustion. -/
def exhausted : PyM σ α := fun _ => .error .timeout

/-- A faithful Python exception. State is RETAINED — that is the layer order. -/
def raisePy (e : PyErr) : PyM σ α := throw e

/-- Lift a pure `Res` worker (the shared trunk's arithmetic, indexing, rendering)
into the monad at the current state. This is the single door every reused worker
comes through. -/
def liftRes : Res α → PyM σ α
  | .ok a          => pure a
  | .exn e         => raisePy e
  | .timeout       => exhausted
  | .unsupported m => refuse m

/-- Lift an ALREADY-APPLIED `Run` value — a trunk helper that is `Run`-typed but
fuel-free and defined outside the mutual block, `attrReadResult` being the one
consumer. The run carries its own successor state, so the incoming state is
discarded: it is the state the helper was applied to. -/
def liftRunAt : Run σ α → PyM σ α
  | .ok s' a       => fun _ => .ok (.ok a, s')
  | .exn s' e      => fun _ => .ok (.error e, s')
  | .timeout       => exhausted
  | .unsupported m => refuse m

/-! ## §3 THE FRAME/WORLD ZOOM

`Run.withLocals` and `Run.toWorld` are the trunk's two state adapters. Their
monadic twins are below, and each is PROVED to agree with its trunk original —
so the rebuild's call boundary is the same boundary, not a similar one. -/

/-- Run a `World`-typed step (a nested call) inside a frame: the world threads,
this frame's locals ride through unchanged — on success AND on a raise. -/
def inFrame (locals : REnv) (x : SemW α) : SemF α := fun st =>
  match x st.world with
  | .error h   => .error h
  | .ok (r, w) => .ok (r, ⟨w, locals⟩)

/-- Enter a fresh frame with the given locals and project back to the world
(returning from a call: the frame's locals die, the shared world survives). -/
def inWorld (locals : REnv) (x : SemF α) : SemW α := fun w =>
  match x ⟨w, locals⟩ with
  | .error h    => .error h
  | .ok (r, st) => .ok (r, st.world)

theorem inFrame_toRun (locals : REnv) (x : SemW α) (st : FrameState) :
    toRun (inFrame locals x) st = Run.withLocals locals (toRun x st.world) := by
  simp only [toRun, inFrame, Run.withLocals]
  rcases h : x st.world with l | ⟨v, w⟩
  · rcases l with _ | m <;> simp
  · rcases v with a | e <;> simp

theorem inWorld_toRun (locals : REnv) (x : SemF α) (w : World) :
    toRun (inWorld locals x) w = Run.toWorld (toRun x ⟨w, locals⟩) := by
  simp only [toRun, inWorld, Run.toWorld]
  rcases h : x ⟨w, locals⟩ with l | ⟨v, st⟩
  · rcases l with _ | m <;> simp
  · rcases v with a | e <;> simp

end LeanModels.Python.Monadic
