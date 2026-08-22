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

/-- **The model giving up** — never a statement about the program.

Both arms DISCARD state, which is what distinguishes them from a language-level
raise: there is no meaningful world to hand back, because the model stopped
rather than the program.

A tier that needs more than two causes does **not** extend this type; it adds an
`.except` layer of its own, which composes for free (C's three never-pooled UB
causes are the worked example, §3.4). -/
inductive Loud where
  /-- Fuel exhaustion, and only fuel exhaustion. -/
  | timeout
  /-- The loud, fuel-INDEPENDENT semantic frontier: outside the modelled tier.
  Never a fabricated answer, never a silent degrade. -/
  | unsupported (msg : String)
deriving Repr, Inhabited, BEq, DecidableEq

/-- The base monad: a run either produces a value or HALTS loudly. -/
abbrev Halt := Except Loud

/-- **The family's semantic monad.** `W` is the tier's world, `ρ` its own raise
payload. See this file's header for why the layer order is not negotiable. -/
abbrev SemM (W : Type) (ρ : Type) := ExceptT ρ (StateT W Halt)

/-- The `PostShape` that goes with `SemM W ρ`. `@[spec]` is a builtin attribute
needing no import at all; `Std.Tactic.Do` is imported here only for the seam in
§0, and consumers inherit both. -/
abbrev SemPS (W : Type) (ρ : Type) : PostShape :=
  .except ρ (.arg W (.except Loud .pure))

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
def refuse (msg : String) : SemM W ρ α := fun _ => .error (.unsupported msg)

/-- Fuel exhausted. -/
def exhausted : SemM W ρ α := fun _ => .error .timeout

/-- The language's own raise. State-RETAINING — this is the channel the layer
order exists to keep world-aware. -/
def raiseIn (e : ρ) : SemM W ρ α := throw e

/-! ## §2 THE STATE ZOOM

A nested call runs in a SMALLER state than its caller (a frame's locals die with
the frame; the shared world survives). These two are that boundary, stated once
for every tier: `W` is the shared part, `L` the part the inner run adds. -/

/-- Run an inner `W`-typed computation inside an outer `W × L`-shaped state,
carrying `l` through unchanged — on success AND on a raise. -/
def zoomIn (get : S → W) (put : S → W → S) (x : SemM W ρ α) : SemM S ρ α :=
  fun s => match x (get s) with
    | .error h   => .error h
    | .ok (r, w) => .ok (r, put s w)

/-- Enter a fresh inner state, run, and project back out. -/
def zoomOut (mk : W → S) (prj : S → W) (x : SemM S ρ α) : SemM W ρ α :=
  fun w => match x (mk w) with
    | .error h   => .error h
    | .ok (r, s) => .ok (r, prj s)

/-! ## §3 THE LAYER ORDER, DECIDED BY `rfl` — the evidence, not the claim -/

section LayerOrder
variable (W ρ : Type)

/-- The WRONG order (`StateT` outside): the failure barrel cannot mention `W`. -/
example : ExceptConds (.arg W (.except ρ (.except Loud .pure)))
    = ((ρ → ULift Prop) × (Loud → ULift Prop) × Unit) := rfl

/-- The RIGHT order — this file's `SemPS`: the `ρ` barrel SEES the world. -/
example : ExceptConds (SemPS W ρ)
    = ((ρ → W → ULift Prop) × (Loud → ULift Prop) × Unit) := rfl

/-- **The `WPMonad` instance synthesizes with ZERO instances written anywhere.**
`ExceptT`, `StateT` and `Except` each ship one at the pin and they compose. This
is the single fact that makes "one vcgen for the family" cost nothing. -/
example : WPMonad (SemM W ρ) (SemPS W ρ) := inferInstance

end LayerOrder

end LeanModels
