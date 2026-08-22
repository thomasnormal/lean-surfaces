/-
**The monadic rebuild's SUBSTRATE, instantiated for Python** —
`docs/python-monadic-rebuild.md` is its plan.

**THE STACK ITSELF LIVES IN `LeanModels/Core/Outcome.lean`** and is language-
neutral. This file does exactly three things that are Python's:

1. instantiates `SemM` at Python's raise payload (`PyErr`) and its two state
   types (`World` for a call, `FrameState` for a frame);
2. proves `Run σ α` — the trunk's outcome type — **IS** that stack, both
   directions; and
3. proves the two frame/world adapters equal to the trunk's own
   (`Run.withLocals`, `Run.toWorld`), so the rebuild's call boundary is the SAME
   boundary rather than a similar one.

**Why the iso lives here and not in Core.** `Run` is declared in
`LeanModels/Python/Runtime.lean`; Core cannot import a language lane without
inverting the dependency, and moving `Run` is deliberately not part of the Core
landing (`Core/Outcome.lean`'s header prices that). So the stack is neutral, the
VIEW is Python's, and each sits where its types are.

**THE BOUNDARY.** `LeanModels/Python/Monadic/` is a PRESENTATION sibling, not a
VERSION sibling: it claims the same edition as the trunk (CPython 3.9), the same
oracle and the same corpus, and it re-presents the trunk's semantics in
do-notation. §1.1's `<Lang>/<Ver>/` convention does not apply to it. Nothing here
is imported by `LeanModels/Python.lean` while the trunk is authoritative.

**WHAT IS SHARED, AND IT IS THE MAXIMAL TRUNK.** Every pure worker of
`LeanModels/Python/Semantics.lean` — `evalBinOp`, `indexValH`, `sliceVal`,
`truthyH`, `assignToH`, `attrCallPlan`, the string workers, the render workers —
is REUSED verbatim. The rebuild re-presents the interpreter's CONTROL, not its
arithmetic; a second copy of `evalBinOp` would be a second thing to keep true.

Zero `sorry`. Zero `native_decide`. `#print axioms` on every theorem.
-/
import LeanModels.Core.Outcome
import LeanModels.Python.Semantics

open LeanModels LeanModels.Python

namespace LeanModels.Python.Monadic

/-- Python's instantiation of the family stack: the raise payload is `PyErr`. -/
abbrev PyM (σ : Type) := SemM σ PyErr

/-- Statement/expression execution transforms a `FrameState`. -/
abbrev SemF := PyM FrameState

/-- A nested call passes only the `World` through. -/
abbrev SemW := PyM World

/-! ## §1 THE ISOMORPHISM — `Run σ` IS the family stack, proved both ways

This is the fact that makes `Core/Outcome.lean` a *destination* rather than a
second design: the trunk's outcome type was already this stack, unrecognised.
It is also what lets `callInMono` have `callIn`'s type, so the two interpreters
are compared by the same harnesses at the same boundary. -/

/-- `Run σ α` as a `PyM σ α`. -/
def ofRun (r : σ → Run σ α) : PyM σ α := fun s =>
  match r s with
  | .ok s' a       => .ok (.ok a, s')
  | .exn s' e      => .ok (.error e, s')
  | .timeout       => .error .timeout
  | .unsupported m => .error (.unsupported m)

/-- A `PyM σ α` as a `Run σ α`. This is the RUNNER's boundary. -/
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

/-! ## §2 PYTHON'S NAMED REFUSALS

`refuse` and `exhausted` come from Core unchanged. Two more are Python's: its
own raise, and the door every reused trunk worker comes through. -/

/-- A faithful Python exception. State is RETAINED — that is the layer order. -/
def raisePy (e : PyErr) : PyM σ α := raiseIn e

/-- Lift a pure `Res` worker (the trunk's arithmetic, indexing, rendering) into
the monad at the current state. **This is the single door the maximal trunk comes
through**, and it is why the rebuild owns no arithmetic of its own. -/
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

/-! ## §3 THE FRAME/WORLD ZOOM, and it AGREES with the trunk

Core's `zoomIn`/`zoomOut` are the general shape; these are Python's two
instances, and each is PROVED equal to the trunk combinator it replaces. Without
those two theorems the rebuild's call boundary would merely resemble the trunk's. -/

/-- Run a `World`-typed step (a nested call) inside a frame: the world threads,
this frame's locals ride through unchanged — on success AND on a raise.

It takes NO locals argument, unlike the trunk's `Run.withLocals`: the locals a
returning call restores are always the ones the frame already had, so passing
them was an opportunity to pass the wrong ones. The theorem below pins the
agreement at exactly that instantiation. -/
def inFrame (x : SemW α) : SemF α :=
  zoomIn FrameState.world (fun st w => { st with world := w }) x

/-- Enter a fresh frame with the given locals and project back to the world
(returning from a call: the frame's locals die, the shared world survives). -/
def inWorld (locals : REnv) (x : SemF α) : SemW α :=
  zoomOut (fun w => ⟨w, locals⟩) FrameState.world x

theorem inFrame_toRun (x : SemW α) (st : FrameState) :
    toRun (inFrame x) st = Run.withLocals st.locals (toRun x st.world) := by
  simp only [toRun, inFrame, zoomIn, Run.withLocals]
  rcases h : x st.world with l | ⟨v, w⟩
  · rcases l with _ | m <;> simp
  · rcases v with a | e <;> simp

theorem inWorld_toRun (locals : REnv) (x : SemF α) (w : World) :
    toRun (inWorld locals x) w = Run.toWorld (toRun x ⟨w, locals⟩) := by
  simp only [toRun, inWorld, zoomOut, Run.toWorld]
  rcases h : x ⟨w, locals⟩ with l | ⟨v, st⟩
  · rcases l with _ | m <;> simp
  · rcases v with a | e <;> simp

end LeanModels.Python.Monadic
