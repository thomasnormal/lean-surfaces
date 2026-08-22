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

end LeanModels
