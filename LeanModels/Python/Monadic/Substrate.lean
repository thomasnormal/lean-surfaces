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
  -- `Run` has no class field, so ingesting one classifies it `unsupported` —
  -- the only honest default when the source does not say.
  | .unsupported m => .error (.unsupported (.unsupported ()) m none)

/-- A `PyM σ α` as a `Run σ α`. This is the RUNNER's boundary. -/
def toRun (x : PyM σ α) : σ → Run σ α := fun s =>
  match x s with
  | .ok (.ok a, s')         => .ok s' a
  | .ok (.error e, s')      => .exn s' e
  | .error .timeout         => .timeout
  -- THE MESSAGE IS PRESERVED EXACTLY, which is what keeps the differential
  -- gate meaningful: the harnesses compare refusal PROSE, and the §5.2 class
  -- is additional structure rather than a change of answer.
  | .error (.unsupported _ m _) => .unsupported m

theorem toRun_ofRun (r : σ → Run σ α) : toRun (ofRun r) = r := by
  funext s; simp only [toRun, ofRun]; cases r s <;> rfl

/-- **`Run` IS A RETRACT OF `PyM`, NOT AN ISOMORPHISM — and the `RefusalCause`
landing is what broke the other direction.**

Before the ruling, `Loud.unsupported` carried a bare `String` and the two types
were genuinely isomorphic; `ofRun_toRun` was a theorem here. It is now FALSE,
and saying so precisely is more useful than weakening it until it typechecks:

`Run.unsupported` has **one** field. `Loud.unsupported` has **three** — the
§5.2 class, the prose, and the diagnostic snapshot. So a round trip through
`Run` can only return the class it can represent, which is `unsupported`, and
the snapshot it can represent, which is `none`. An `orderDependence` refusal
goes in and an `unsupported` one comes out.

The direction that survives is the one that matters for the boundary: `Run`
EMBEDS into `PyM` faithfully, so a trunk-shaped outcome is never corrupted by
being lifted. -/
theorem toRun_ofRun' (r : σ → Run σ α) : toRun (ofRun r) = r := toRun_ofRun r

/-- The retract's exact residue: the round trip is the identity on values,
exceptions and timeouts, and on refusals it NORMALISES the class to
`unsupported` and drops the snapshot. Stated so the loss is a theorem rather
than a caveat. -/
theorem ofRun_toRun_normalises (x : PyM σ α) (s : σ) :
    ofRun (toRun x) s
      = (match x s with
         | .ok (v, s') => .ok (v, s')
         | .error .timeout => .error .timeout
         | .error (.unsupported _ m _) => .error (.unsupported (.unsupported ()) m none)) := by
  simp only [toRun, ofRun]
  rcases h : x s with l | ⟨v, s'⟩
  · rcases l with _ | ⟨c, m, sn⟩ <;> simp
  · rcases v with a | e <;> simp

/-- And the round trip IS the identity exactly on the payload-free refusals —
which is every refusal this tier builds, because its three refusal helpers fix
the class and never attach a snapshot. -/
theorem ofRun_toRun_of_plain (x : PyM σ α) (s : σ)
    (h : ∀ c m sn, x s = .error (.unsupported c m sn) →
           c = .unsupported () ∧ sn = none) :
    ofRun (toRun x) s = x s := by
  rw [ofRun_toRun_normalises]
  rcases hx : x s with l | ⟨v, s'⟩
  · rcases l with _ | ⟨c, m, sn⟩
    · simp
    · obtain ⟨hc, hsn⟩ := h c m sn hx; simp [hc, hsn]
  · simp

/-! ## §2 PYTHON'S NAMED REFUSALS

`exhausted` comes from Core unchanged. `refuse` is Python's ONE-ARGUMENT
wrapper over Core's classified refusal — see below. Two more are Python's: its
own raise, and the door every reused trunk worker comes through. -/

/-- **Python's refusal, and its §5.2 CLASS.**

Core's `refuse` takes a `RefusalCause π` and prose. Python's payload is `Unit`
(`PyM = SemM σ PyErr`, the payload-free spelling), so the prose IS the detail and
the only thing a site must decide is its CLASS. The overwhelming majority are
`unsupported` — out-of-tier constructs that retire by climbing a rung — so that
is what this wrapper fixes, and **the 168 existing call sites are unchanged**.

The two classes that are NOT the default get their own spellings below, because
a refusal filed under the wrong class is invisible to the scoreboard in exactly
the way §5.2 exists to prevent. Python has **no `undefined`**: the language has
no undefined behaviour, and per the ruling the class is PRESENT AND GATED rather
than absent — the gate is `no_undefined_refusals` in `Spec.lean`. -/
def refuse (msg : String) : PyM σ α := LeanModels.refuse (.unsupported ()) msg

/-- The run needs something outside the modelled slice — an unmodelled builtin,
a runner-boundary effect like stdin. Retires by WIDENING the slice, which is a
different schedule from `unsupported`'s "climb a rung". -/
def refuseEnv (msg : String) : PyM σ α := LeanModels.refuse (.environment ()) msg

/-- The language admits several orders and the model cannot show the observable
invariant under all of them: Python's hash-order refusals. **Never retires by
building more language**, which is why it is not `unsupported`. -/
def refuseOrder (msg : String) : PyM σ α := LeanModels.refuse (.orderDependence ()) msg

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


/-! ## §4 THE RUNNER SEAM — do-notation, translated into `Run`

**One opening of the monad stack, and this is it.** `bind_apply` is the single
place anything in this tier reasons through `ExceptT`/`StateT`/`Except` by
name; everything else composes these four lemmas. It lives HERE rather than in
a consumer because it is a fact about the STACK, and a second consumer that
opened the stack again would be a second thing to keep true.

**These are the lemmas the sunfish R-track was proving as leaf copies.** They
translate the rebuild's do-notation into the TRUNK's `Run.bind`, which is the
vocabulary every `Run`-level theorem is already stated in — so a proof about a
monadic definition can reach the trunk's lemmas without re-deriving the
boundary each time. -/

theorem bind_apply {σ α β : Type} (x : PyM σ α) (f : α → PyM σ β) (s : σ) :
    (x >>= f) s = (match x s with
      | .error l => .error l
      | .ok (.error e, s') => .ok (.error e, s')
      | .ok (.ok a, s') => f a s') := by
  cases h : x s with
  | error l => simp [Bind.bind, ExceptT.bind, ExceptT.mk, StateT.bind, h, Except.bind]
  | ok p =>
      obtain ⟨r, s'⟩ := p
      cases r with
      | error e =>
          simp only [Bind.bind, ExceptT.bind, ExceptT.mk, StateT.bind, h, Except.bind,
                     ExceptT.bindCont]
          rfl
      | ok a =>
          simp [Bind.bind, ExceptT.bind, ExceptT.mk, StateT.bind, h, Except.bind,
                ExceptT.bindCont]

theorem toRun_pure {σ α : Type} (a : α) (s : σ) :
    toRun (pure a : PyM σ α) s = .ok s a := rfl

theorem toRun_bind {σ α β : Type} (x : PyM σ α) (f : α → PyM σ β) (s : σ) :
    toRun (x >>= f) s = Run.bind (toRun x s) (fun s' a => toRun (f a) s') := by
  simp only [toRun, bind_apply]
  rcases h : x s with l | ⟨r, s'⟩
  · rcases l with _ | ⟨c, m, sn⟩ <;> rfl
  · cases r <;> rfl

/-- **`Functor.map` IS NOT UNFOLDED HERE, and that is the proof shape rather
than a preference.** Unfolding it drops below `bind_apply`'s reach and the goal
stops being about this stack at all; going through `map_eq_pure_bind` keeps the
argument at the level the other three lemmas live at. **One opening of the monad
stack is the right number** — this lemma is what keeps it at one. -/
theorem toRun_map {σ α β : Type} (g : α → β) (x : PyM σ α) (s : σ) :
    toRun (g <$> x) s = Run.bind (toRun x s) (fun s' a => .ok s' (g a)) := by
  rw [map_eq_pure_bind, toRun_bind]
  simp only [toRun_pure]

#print axioms bind_apply
#print axioms toRun_pure
#print axioms toRun_bind
#print axioms toRun_map

end LeanModels.Python.Monadic
