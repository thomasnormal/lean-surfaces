/-
# `SemM` — THE FAMILY'S SHARED SEMANTIC MONAD

`docs/family-architecture.md` §3.4 designs this stack and §3.8 names this file as
its destination. It is landed here, once, so that **no tier ever writes its own
copy** — §3.8's rule in its own words: *"a second interpreter landing with its own
copy is a defect, not a design."*

**The trigger fired because a lane arrived.** §3.8 lists three candidates and says
whichever lands first is the trigger. The Python rebuild lane's `SemM` is the
first, and the SystemVerilog lane blocked on it rather than defining an SV-local
stack — which is the rule working as intended.

## THE STACK, and the layer order is LOAD-BEARING

```
SemM W ρ  =  ExceptT ρ (StateT W (Except Loud))
```

Two failure channels, and they are not interchangeable:

* **`ρ` — the language's own raise.** State-RETAINING. A Python `except` clause,
  a C `longjmp`, an SV disable — the world the raise happened in survives, and
  the handler sees it.
* **`Loud` — the MODEL giving up.** State-DISCARDING, and never a claim about the
  language. `timeout` is fuel exhaustion; `unsupported` is the loud, fuel-
  INDEPENDENT semantic frontier. A tier that answers `unsupported` has said *"I
  do not model this"*, which is the family's central honesty device (§0.1).

**`StateT` OUTSIDE `ExceptT` DISCARDS THE STATE ON A RAISE, and that order cannot
state a state-aware error postcondition.** The two shapes are `W → Except ρ (α × W)`
versus `W → (Except ρ α × W)`; only the second keeps `W` on the error branch. The
difference is visible in the `PostShape` barrel — `ρ → ULift Prop` in the wrong
order, `ρ → W → ULift Prop` in the right one — and it is decided by `rfl` in §3
below rather than asserted. This document's own first draft had it backwards.

## FUEL IS NOT IN HERE, and that is a measurement

Fuel is an index on the step function, never a monad layer. Not a preference: as
a layer it **does not typecheck** — fuel's job is to BE the recursion argument,
so hidden in state it is not an argument and the interpreter fails to show
termination. A tier decides fuel's placement BEFORE writing its interpreter
(§3.4's founding-checklist item); `LeanModels/Python/Monadic/Eval.lean` records
one worked answer, splitting the interpreter into a fuel-free structural half and
a fuel-structural knot.

## FOR THE C AND ES TIERS: your `.ok` arm IS `Except`'s

Both tiers already spell the base as their own inductive with three arms —
`.ok`, `.timeout`, `.unsupported`. Here it is `Except (Loud π σ)`, and the two
are ISOMORPHIC:

| your constructor | here |
| --- | --- |
| `.ok a` | `Except.ok a` |
| `.timeout` | `Except.error .timeout` |
| `.unsupported …` | `Except.error (.unsupported …)` |

**Nothing is lost and the deviation is deliberate**, for a measured reason: the
whole stack synthesizes a `WPMonad` with ZERO instances written *because* the
base is `Except`. A bespoke `.ok`-carrying inductive has no such instance, and
the substrate's central property would have been traded for a spelling. Your
payloads are lifted exactly — C's snapshot and its never-an-observable guard,
ES's cause-plus-message — only the constructor spelling differs.

## WHAT IS DELIBERATELY NOT HERE

**`Run`.** §3.8's destination clause also wants Python's `Run` moved here with
`Runtime.lean` re-exporting. That half is **not** in this landing, and the reason
is a measurement, not reluctance: `Run` lives in `LeanModels/Python/Runtime.lean`,
which sits under the `LeanModels` umbrella that **65 files under `Examples/`**
import, and moving it re-founds an import graph the sunfish campaign is mid-flight
in. **The substance of §3.8's rule is satisfied without it** — the family has ONE
stack, in one file, and `Run` is *proved* to be a view of it
(`LeanModels/Python/Monadic/Substrate.lean`: `ofRun`/`toRun` mutually inverse).
A lane arriving by either route finds one artifact. Moving the datatype is an
erosion item, payable when the campaign's files are being touched anyway.

## THE STACK SPELLING — hand-stacked, and `EStateM` is NOTED not ADOPTED

`EStateM ε σ` is this corrected order *already instantiated*, and it arrives with
seven `Spec` lemmas for free. It is deliberately **not** what this file uses, and
the reason is a measurement rather than a preference: **kernel `rfl` through
`EStateM` is 1.4× SLOWER at fuel 4096 (50.1 s vs 35.3 s)**. Kernel reducibility is
load-bearing here — it is what lets a tier `#guard` its interpreter on real
fixtures instead of admiring it, and it is what the Python rebuild's whole
fuel-boundary design rests on. A tier that wants the free spec lemmas more than
it wants fast kernel reduction can build the isomorphism; it is available, and it
is not the default.

Nothing in this file mentions any language. Zero `sorry`, zero `native_decide`.
-/
import LeanModels.Core.Order
import Std.Do
import Std.Tactic.Do

open Std.Do

namespace LeanModels

/-! ## §0.5 REFUSAL CAUSES — the family's FOUR classes, the tier's payload

`docs/family-architecture.md` §5.2 + the `RefusalCause` ruling (`14bdd7a`):

> **`Core` carries the FOUR §5.2 CLASSES as a four-constructor type,
> PARAMETERIZED by a tier payload — `RefusalCause π`. The classes are family
> law; the payload is the tier's.**

The four retire on **completely different schedules**, which is why pooling them
makes a scoreboard unreadable.

**AN EXPECTED-EMPTY CLASS IS PRESENT AND GATED, NEVER ABSENT.** Omitting
`undefined` because a language has no undefined behaviour makes the emptiness a
fact about the TYPE, invisible to the scoreboard — it cannot tell *"this
language has no UB"* from *"this tier did not model that column."* A gate needs
a constructor to be about. -/
inductive RefusalCause (π : Type) where
  /-- Out-of-tier construct. Retires by climbing a rung. -/
  | unsupported (detail : π)
  /-- The language says this run has no meaning — C's UB, Ada's erroneous
  execution. **Never retires: it is the product.** -/
  | undefined (detail : π)
  /-- The run needs something outside the modeled slice. Retires by widening it. -/
  | environment (detail : π)
  /-- The language admits several orders and the model cannot show the
  observable invariant under all of them. -/
  | orderDependence (detail : π)
deriving Repr, Inhabited, BEq

/-- The §5.2 class name, emitted verbatim. **A scoreboard buckets on THIS, never
by parsing the payload's prose** — the entire reason the class is a constructor
and not a string convention. -/
def RefusalCause.className : RefusalCause π → String
  | .unsupported _     => "unsupported"
  | .undefined _       => "undefined"
  | .environment _     => "environment"
  | .orderDependence _ => "order-dependence"

/-- Is this the never-retiring class? **Lifted from ES so the gate is written
once.** A tier whose language has no undefined behaviour gates on this being
false everywhere; a tier that has UB uses it to count its own product. -/
def RefusalCause.isUndefined : RefusalCause π → Bool
  | .undefined _ => true
  | _ => false

/-- The class that does not retire by building more language. -/
def RefusalCause.isOrderDependence : RefusalCause π → Bool
  | .orderDependence _ => true
  | _ => false

/-- The tier's payload, class-blind. -/
def RefusalCause.detail : RefusalCause π → π
  | .unsupported d | .undefined d | .environment d | .orderDependence d => d

/-- **The model giving up** — never a statement about the program. Both arms
DISCARD state: there is no meaningful world to hand back, because the MODEL
stopped rather than the program.

## The payload SUBSUMES the two tiers that already implemented rulings

Core's original `msg : String` was the poorest of the three shapes in the tree,
and convergence-by-import would have deleted two implemented rulings:

* **C** (`C23/Memory.lean`) carries `(what : String) (snapshot : Option Mem)` —
  the Halt ruling's structured payload, with the never-an-observable guard made
  STRUCTURAL rather than advisory.
* **ES** (`Es/Completion.lean`) carries `(cause : EsRefusal) (message : String)`
  — the `RefusalCause` ruling.

So the payload here is the union of both, parameterized: `π` is the cause
detail (C: a J.2 index; ES: a host-hook name; Python: `Unit`, its prose living
in `message`), and `σ` is the diagnostic snapshot (C: `Mem`; ES and Python:
`Unit`, always `none`).

**THE SNAPSHOT IS DIAGNOSTIC ONLY AND IS NEVER AN OBSERVABLE**, and that guard
is lifted into Core so no tier re-implements it: the `BEq` below IGNORES it, and
`Loud.observable` drops it. Two runs that refused the same construct compare
EQUAL even if they reached it through different states. A derived `BEq` would
have compared it and quietly made a diagnostic aid part of the verdict. -/
inductive Loud (π : Type) (σ : Type) where
  /-- Fuel exhaustion, and nothing else. Carries NO state: a timeout is not an
  observation, and state here would invite treating it as one. -/
  | timeout
  /-- The loud, fuel-INDEPENDENT semantic frontier, carrying its §5.2 CLASS, its
  prose, and optionally a diagnostic snapshot. -/
  | unsupported (cause : RefusalCause π) (message : String) (snapshot : Option σ)
deriving Repr, Inhabited

/-- **The snapshot guard, enforced structurally.** Lifted from C's instance so
that no tier writes it again — and so that a tier which forgets to cannot
silently promote a diagnostic into a verdict. -/
instance [BEq π] : BEq (Loud π σ) where
  beq
    | .timeout, .timeout => true
    | .unsupported c m _, .unsupported c' m' _ => c == c' && m == m'
    | _, _ => false

/-- The OBSERVABLE projection: class, prose, and **no snapshot**. This is the
second place the guard is enforced — there is nowhere to put a `σ` here, so a
snapshot cannot reach a comparison even by accident. -/
def Loud.observable : Loud π σ → String × String
  | .timeout => ("timeout", "")
  | .unsupported c m _ => (c.className, m)

/-- The base monad: a run either produces a value or HALTS loudly.

**SPELLED AS `Except (Loud π σ)`, NOT as a custom `.ok`-carrying inductive** —
which is the ONE place this does not lift C's and ES's spelling literally, and
the reason is measured: `Except` composes a `WPMonad` for the whole stack with
ZERO instances written, and a bespoke inductive base would have none. The two
are isomorphic (`.ok` ↔ `.ok`, `timeout`/`unsupported` ↔ `.error _`), so the
tiers' information is preserved exactly; only the constructor spelling differs. -/
abbrev HaltWith (π : Type) (σ : Type) := Except (Loud π σ)

/-- The payload-free instantiation, which is what a tier with no structured
cause detail and no diagnostic snapshot writes. **`Halt` and `SemM` keep their
original arities**, so every tier that adopted the substrate before the
`RefusalCause` ruling imports with ZERO edits.

Default arguments were tried first and do NOT work here: an `abbrev` returning a
monad is applied to its VALUE type positionally, so `SemM W ρ Int` binds `Int`
to `π` and yields a `Type → Type` rather than a type. Two abbrevs, and the
`rfl`s below pin that the short one really is the `Unit` instantiation. -/
abbrev Halt := HaltWith Unit Unit

/-- **The family's semantic monad.** `W` is the tier's world, `ρ` its own raise
payload. See this file's header for why the layer order is not negotiable. -/
abbrev SemMWith (W : Type) (ρ : Type) (π : Type) (σ : Type) :=
  ExceptT ρ (StateT W (HaltWith π σ))

/-- The spelling every payload-free tier writes, unchanged from before the
ruling. -/
abbrev SemM (W : Type) (ρ : Type) := SemMWith W ρ Unit Unit

/-- The `PostShape` that goes with `SemM W ρ`. `@[spec]` is a builtin attribute
needing no import at all; `Std.Tactic.Do` is imported here only for the seam in
§0, and consumers inherit both. -/
abbrev SemPSWith (W : Type) (ρ : Type) (π : Type) (σ : Type) : PostShape :=
  .except ρ (.arg W (.except (Loud π σ) .pure))

/-- The payload-free `PostShape`. -/
abbrev SemPS (W : Type) (ρ : Type) : PostShape := SemPSWith W ρ Unit Unit

/-! ## §0 `grind` IS WIRED INTO `mvcgen`'s OWN EXTENSION SEAM

`mvcgen_trivial_extensible` is core's documented seam — its docstring says
*"users are encouraged to extend `mvcgen_trivial_extensible`"* precisely so that
the default `(try mpure_intro); trivial` is not overridden. One line puts `grind`
behind it for every tier that imports Core.

**Measured, twice.** On the pilot's own gate: **12 verification conditions → 0**,
the entire closing script deleted, identical axioms. Re-measured on the Python
rebuild's two faithful-interpreter gates (`assign_binop_M`,
`subscript_global_M`): both close with their closing scripts **deleted
outright** — `mvcgen [execOpen, evalOpen]` and nothing else — and the file
elaborates no slower.

It compounds, which is why it belongs in Core rather than in one tier: `grind`
draws on `@[grind]`-tagged facts, and Std's container lemmas are already tagged
151 times over. A tier's own `@[spec]`-adjacent simp facts should be tagged
`@[grind]` where natural, and they then serve every VC in the family. -/

macro_rules | `(tactic| mvcgen_trivial_extensible) => `(tactic| grind)

/-! ## §1 THE NAMED REFUSAL PRIMITIVES

**Never a bare polymorphic `throw` in interpreter code.** This is forced by a
real bug in `Std` at the pinned toolchain — `Spec.throw_Except` carries binders
its conclusion does not determine, so a bare `throw` yields universe-level
metavariables and the declaration is REJECTED — and it is what this family wants
anyway: a refusal is a first-class notion here, and `mvcgen` rewards making it
one. Every failure below is a named constant that can carry an `@[spec]` lemma. -/

/-- Outside the modelled tier. Loud, fuel-independent, state-discarding. -/
def refuse (cause : RefusalCause π) (message : String) : SemMWith W ρ π σ α :=
  fun _ => .error (.unsupported cause message none)

/-- A refusal carrying its diagnostic snapshot. Separate from `refuse` so that
attaching one is a DELIBERATE act at the site that has the state — and so that
the common case cannot accidentally carry one. -/
def refuseWith (cause : RefusalCause π) (message : String) (snap : σ) :
    SemMWith W ρ π σ α :=
  fun _ => .error (.unsupported cause message (some snap))

/-- Fuel exhausted. -/
def exhausted : SemMWith W ρ π σ α := fun _ => .error .timeout

/-- The language's own raise. State-RETAINING — this is the channel the layer
order exists to keep world-aware. -/
def raiseIn (e : ρ) : SemMWith W ρ π σ α := throw e

/-! ## §2 THE STATE ZOOM

A nested call runs in a SMALLER state than its caller (a frame's locals die with
the frame; the shared world survives). These two are that boundary, stated once
for every tier: `W` is the shared part, `L` the part the inner run adds. -/

/-- Run an inner `W`-typed computation inside an outer `W × L`-shaped state,
carrying `l` through unchanged — on success AND on a raise. -/
def zoomIn (get : S → W) (put : S → W → S) (x : SemMWith W ρ π σ α) : SemMWith S ρ π σ α :=
  fun s => match x (get s) with
    | .error h   => .error h
    | .ok (r, w) => .ok (r, put s w)

/-- Enter a fresh inner state, run, and project back out. -/
def zoomOut (mk : W → S) (prj : S → W) (x : SemMWith S ρ π σ α) : SemMWith W ρ π σ α :=
  fun w => match x (mk w) with
    | .error h   => .error h
    | .ok (r, s) => .ok (r, prj s)

/-! ## §3 THE LAYER ORDER, DECIDED BY `rfl` — the evidence, not the claim -/

section LayerOrder
variable (W ρ π σ : Type)

/-- The WRONG order (`StateT` outside): the failure barrel cannot mention `W`. -/
example : ExceptConds (.arg W (.except ρ (.except (Loud π σ) .pure)))
    = ((ρ → ULift Prop) × (Loud π σ → ULift Prop) × Unit) := rfl

/-- The RIGHT order — this file's `SemPS`: the `ρ` barrel SEES the world. -/
example : ExceptConds (SemPSWith W ρ π σ)
    = ((ρ → W → ULift Prop) × (Loud π σ → ULift Prop) × Unit) := rfl

/-- **The `WPMonad` instance synthesizes with ZERO instances written anywhere.**
`ExceptT`, `StateT` and `Except` each ship one at the pin and they compose. This
is the single fact that makes "one vcgen for the family" cost nothing. -/
example : WPMonad (SemMWith W ρ π σ) (SemPSWith W ρ π σ) := inferInstance

/-- AND at the short spelling, which is the one eleven tiers write. -/
example : WPMonad (SemM W ρ) (SemPS W ρ) := inferInstance

/-- The short spellings ARE the `Unit` instantiations — pinned, not assumed. -/
example : SemM W ρ = SemMWith W ρ Unit Unit := rfl
example : Halt = HaltWith Unit Unit := rfl
example : SemPS W ρ = SemPSWith W ρ Unit Unit := rfl

end LayerOrder

/-! ## §4 THE RUN SEAM — one opening, and the rest of the stack is corollaries

**RATIFIED BY CONVERGENCE (§9.3), and the convergence IS the argument.**
Two tiers wrote this lemma independently and neither saw the other's:
`LeanModels/Go/Obs.lean` §1 for `GoM`, and the C tier's Rung A landing for
`EvalM`. Both spellings are `SemMWith`; both proofs are the same five
lines; and **neither mentions a language.** The whole difference between
them is four type substitutions — `GoWorld`/`Mem`, `Panic`/`Refusal`,
`SpecRef`/`CDetail`, `Unit`/`Mem` — which is exactly §9.3's signal for a
shared definition rather than two.

Go's own header drew the line in the right place and put this on the wrong
side of it: *"the ORDER lifts; the CONGRUENCES don't."* That is true of
Python's `Res`, which carries an `.exn` arm this stack does not and whose
`bind` is therefore a different function. It is **not** true of a second
consumer of THIS stack, and the test is mechanical rather than a matter of
judgement:

> **A congruence generic in the SUBSTRATE'S OWN parameters is not a
> per-tier congruence. "The congruences don't lift" is a claim about a
> DIFFERENT monad, never about a second tier that instantiates the same
> one — and which of the two you are looking at is decided by whether the
> proof mentions a tier type.**

**What this section is and is not.** It is `bind`'s opening plus one row
per primitive — the six shapes §3.4 enumerates, minus the two the state
zoom already carries. It adds **theorems only**: no instance, no
`simp`/`grind` attribute, and no change to any existing declaration, so a
tier that has not adopted it elaborates exactly as before. Attributes stay
with the tiers, because a simp set is a tier's proof strategy and not a
family fact — Go's rows are `@[go_run]` and that stays Go's call.

**ADOPTION IS BY TOUCH (§9.2), never big-bang.** The C tier adopts in the
same commit that lands this, because it is the lane that is here. Go's
eleven rows in `Obs.lean` §1-§3 become one-line instances of these
whenever the Go lane next touches that file; nothing asks it to do so
today, and until it does the tree carries two proofs of one fact **in the
open**, which is the honest state and not a silent one. -/

section Seam
variable {W ρ π σ α β : Type}

/-- **THE OPENING.** The one place this stack is unfolded by hand: run the
head, then stop loudly, propagate the raise **with its world**, or continue
with the value in the world it left.

The three arms are the covenant in `bind`'s own shape — `Loud` discards,
`ρ` retains, and only a value continues — which is why the layer order in
this file's header is what makes the lemma statable at all. -/
theorem SemMWith.run_bind (x : SemMWith W ρ π σ α) (f : α → SemMWith W ρ π σ β) (w : W) :
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

/-! ### Stepping a bind from a KNOWN head

**Stated on an `x w = …` hypothesis rather than as congruences**, and the
reason is a Lean fact both tiers hit independently (`docs/backlog/go.md`
§G11): **`simp` will not rewrite inside a match DISCRIMINANT.** Once a
proof has produced `run_bind`'s right-hand side, no amount of rewriting
reduces the scrutinee — the lemma fires on the head *in isolation* and
refuses to fire in that position. These three never produce the match at
all: given what the head DOES, each rewrites the whole bind in one step. -/

/-- The head produced a VALUE: continue with it, in the world it left. -/
theorem SemMWith.run_bind_ok {x : SemMWith W ρ π σ α} {f : α → SemMWith W ρ π σ β}
    {w w' : W} {a : α} (h : x w = .ok (.ok a, w')) : (x >>= f) w = f a w' := by
  rw [SemMWith.run_bind, h]

/-- The head HALTED — fuel exhaustion or an out-of-tier construct. State
discarded, and the bind is that, unchanged. -/
theorem SemMWith.run_bind_loud {x : SemMWith W ρ π σ α} {f : α → SemMWith W ρ π σ β}
    {w : W} {l : Loud π σ} (h : x w = .error l) : (x >>= f) w = .error l := by
  rw [SemMWith.run_bind, h]

/-- The head RAISED: the raise propagates and **the world survives with
it** — the `ρ` channel, which is the whole reason for the layer order. -/
theorem SemMWith.run_bind_raise {x : SemMWith W ρ π σ α} {f : α → SemMWith W ρ π σ β}
    {w w' : W} {e : ρ} (h : x w = .ok (.error e, w')) :
    (x >>= f) w = .ok (.error e, w') := by
  rw [SemMWith.run_bind, h]

/-! ### The primitives, one row each

Each is a constant of the stack, so each gets its own row rather than
being re-derived at every call site: after `run_bind` splits a `do` block,
the head is always one of these. -/

theorem SemMWith.run_pure (a : α) (w : W) :
    (pure a : SemMWith W ρ π σ α) w = .ok (.ok a, w) := rfl

theorem SemMWith.run_get (w : W) :
    (get : SemMWith W ρ π σ W) w = .ok (.ok w, w) := rfl

theorem SemMWith.run_set (w w' : W) :
    (set w' : SemMWith W ρ π σ PUnit) w = .ok (.ok ⟨⟩, w') := rfl

theorem SemMWith.run_modify (f : W → W) (w : W) :
    (modify f : SemMWith W ρ π σ PUnit) w = .ok (.ok ⟨⟩, f w) := rfl

/-- The language's own raise, at the spelling `throw` — which is what a
tier's own named refusal primitives unfold to. State-RETAINING. -/
theorem SemMWith.run_throw (e : ρ) (w : W) :
    (throw e : SemMWith W ρ π σ α) w = .ok (.error e, w) := rfl

/-- §1's named primitive, and the same fact: `raiseIn` IS `throw`. Two
rows because they are two subjects — a tier that routes through §1's name
should not have to unfold it to use the seam. -/
theorem SemMWith.run_raiseIn (e : ρ) (w : W) :
    (raiseIn e : SemMWith W ρ π σ α) w = .ok (.error e, w) :=
  SemMWith.run_throw e w

/-- Fuel exhausted. Carries no world, because a timeout is not an
observation. -/
theorem SemMWith.run_exhausted (w : W) :
    (exhausted : SemMWith W ρ π σ α) w = .error .timeout := rfl

/-- Out of tier, with no diagnostic snapshot. -/
theorem SemMWith.run_refuse (c : RefusalCause π) (m : String) (w : W) :
    (refuse c m : SemMWith W ρ π σ α) w = .error (.unsupported c m none) := rfl

/-- Out of tier, carrying a snapshot. Separate because attaching one is a
DELIBERATE act at the site that has the state. -/
theorem SemMWith.run_refuseWith (c : RefusalCause π) (m : String) (s : σ) (w : W) :
    (refuseWith c m s : SemMWith W ρ π σ α) w = .error (.unsupported c m (some s)) := rfl

/-! ### The corollaries

`map` is `pure`-after-`bind` and `seqRight` is `bind` with the value
dropped, so neither needs a second opening — which is the point of having
exactly one. -/

theorem SemMWith.run_map (g : α → β) (x : SemMWith W ρ π σ α) (w : W) :
    (g <$> x) w
      = (match x w with
         | .error h => .error h
         | .ok (.error e, w') => .ok (.error e, w')
         | .ok (.ok a, w') => .ok (.ok (g a), w')) := by
  rw [map_eq_pure_bind, SemMWith.run_bind]
  cases hx : x w with
  | error h => rfl
  | ok p => obtain ⟨r, w'⟩ := p; cases r <;> rfl

/-- Sequencing without a value — the `do` block's `let _ ← …` shape. -/
theorem SemMWith.run_seqRight (x : SemMWith W ρ π σ α) (y : SemMWith W ρ π σ β) (w : W) :
    (x >>= fun _ => y) w
      = (match x w with
         | .error h => .error h
         | .ok (.error e, w') => .ok (.error e, w')
         | .ok (.ok _, w') => y w') := by
  rw [SemMWith.run_bind]

/-! ### The seam at the SHORT spelling, pinned

`SemM W ρ` is the `Unit` instantiation (§3 decides that by `rfl`), so a
payload-free tier needs no separate row. Checked here rather than assumed
— and checked through `run_bind_ok`, whose statement contains **no match**,
because that is the honest form of the claim: a `match` elaborated at
`Loud Unit Unit` is a DIFFERENT matcher constant from one elaborated at
`Loud π σ`, and an `example` that appeared to compare the two would be
testing matcher elaboration rather than the seam.

> **Two `match` expressions over instantiations of one type are not the
> same term even when they are the same function; state a cross-spelling
> claim on a match-free lemma, or state it about elaboration by
> accident.** -/

example (x : SemM W ρ α) (f : α → SemM W ρ β) (w w' : W) (a : α)
    (h : x w = .ok (.ok a, w')) : (x >>= f) w = f a w' := SemMWith.run_bind_ok h

end Seam

#print axioms SemMWith.run_bind
#print axioms SemMWith.run_map

end LeanModels

/-! ## §8 THE `Lean.Order` BASE INSTANCES — three, and the stack does the rest

`Core/Order.lean` proved `FlatLe` IS `Lean.Order.FlatOrder.rel`. What is left is
the one thing core cannot supply: **the BOTTOM of this family's base monad.**

Core's flat orders bottom out at `Option` (bottom `none`) and at `IO`/`EIO`/`ST`.
It ships no instance for `Except ε` as a monad in its own right and could not:
`Except ε α` is `ExceptT ε Id α`, so the transformer instance would demand
`PartialOrder (Id α)` for an arbitrary `α`. Our bottom is `.error .timeout` — a
CONSTRUCTOR of `Loud` in the base layer — and nothing in core can guess it.

Supply it once and **the entire `ExceptT ρ (StateT W (HaltWith π σ))` stack
synthesises**, because core already carries `PartialOrder`/`CCPO`/`MonoBind` for
`ExceptT` and `StateT`. The three `example`s below are that claim, checked.

**What this does NOT do, deliberately: it restates no tier theorem.** `Res.le`,
`Run.le` and `Monadic.PyLe` keep their spellings, their notations and their
consumers. This is the family fact, landed additively; adopting core's frame in
a tier's PROOFS is a separate decision with its own price
(`docs/lean-order-census.md`). -/

namespace LeanModels
open Lean.Order

/-- The base order: flat, bottomed at the timeout. -/
instance instPartialOrderHaltWith {π σ α : Type} : PartialOrder (HaltWith π σ α) :=
  inferInstanceAs (PartialOrder (FlatOrder (Except.error Loud.timeout : HaltWith π σ α)))

instance instCCPOHaltWith {π σ α : Type} : CCPO (HaltWith π σ α) :=
  inferInstanceAs (CCPO (FlatOrder (Except.error Loud.timeout : HaltWith π σ α)))

/-- `bind` is monotone in both arguments at the base. The two fields ARE the
left and right halves every tier's own `le_bind` proves by hand. -/
instance instMonoBindHaltWith {π σ : Type} : MonoBind (HaltWith π σ) where
  bind_mono_left {α β a₁ a₂ f} h := by
    cases h with
    | bot => exact .bot
    | refl => exact .refl
  bind_mono_right {α β a f₁ f₂} h := by
    cases a with
    | error e => exact .refl
    | ok v    => exact h v

/-- The base instance's `⊑` IS `FlatLe` at the timeout. -/
theorem HaltWith.le_iff_flatLe {π σ α : Type} (x y : HaltWith π σ α) :
    x ⊑ y ↔ FlatLe (Except.error Loud.timeout) x y := (FlatLe.iff_rel x y).symm

/-- **And the order core SYNTHESISES for the whole stack is POINTWISE `FlatLe`**
— which is exactly the shape every tier wrote by hand. This is the theorem that
makes the census's "core covers the stack above its base" checkable. -/
theorem SemMWith.le_iff {W ρ π σ α : Type} (x y : SemMWith W ρ π σ α) :
    x ⊑ y ↔ ∀ s, FlatLe (Except.error Loud.timeout) (x s) (y s) := by
  constructor
  · intro h s; exact (FlatLe.iff_rel _ _).mpr (h s)
  · intro h s; exact (FlatLe.iff_rel _ _).mp (h s)

/-! The stack, synthesised — no instance written above the base. -/
example : PartialOrder (SemMWith Nat String Unit Unit Bool) := inferInstance
example : CCPO (SemMWith Nat String Unit Unit Bool) := inferInstance
example : MonoBind (SemMWith Nat String Unit Unit) := inferInstance

#print axioms HaltWith.le_iff_flatLe
#print axioms SemMWith.le_iff

end LeanModels
