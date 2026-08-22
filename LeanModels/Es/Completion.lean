import LeanModels.Es.Value

/-!
# Completion records, and the monad they are the return discipline of

M2 inch 1, second half. `docs/es-semantics-design.md` §1 is the design;
this is it, in Lean, with no evaluator attached.

## The substrate, adopted BY SHAPE

`docs/family-architecture.md` §3.4 fixes the family's substrate as
`ExceptT ρ (StateT W Halt)`, in that order — the order established there
by `rfl`, because `StateT` outside `ExceptT` discards the state on a raise
and the tier's own error postcondition then cannot be stated.

**ADOPTION NOTE: `LeanModels/Core/` does not yet export a `SemM`, so this
file defines the family's SHAPE locally and will be replaced by the core
export when the extraction lands — it is not a variant.**

The structures census has since ruled (`docs/backlog.md` §L81): rest the
substrate's **two-layer core on `EStateM`** — which is §3.4's corrected
layer order already instantiated in core, with a `WPMonad` for free — and
**keep `Halt` OUTSIDE it**. That is compatible with what is written here,
and not by luck: `ExceptT ρ (StateT W Halt) α` unfolds to

    W → Halt (Except ρ α × W)

so `Halt` is already the OUTERMOST layer and the two inner layers are
exactly the `(Except, State)` pair `EStateM ρ W` spells. Re-spelling those
two is then an internal change with the same unfolding — the census also
measured `EStateM` **~1.4x slower in the kernel**, which is a reason to
take the swap deliberately at the core extraction rather than eagerly
here. Nothing below depends on which combinators spell the pair.

## Why ρ is the WHOLE abrupt completion record

ES2026 §6.2.4 gives a Completion Record four abrupt types — `throw`,
`return`, `break`, `continue` — and writes their propagation as an
OPERATOR: `? Foo(x)` at **2,328** sites in the pinned edition, `! Foo(x)`
at **555**, and `ReturnIfAbrupt` (the ES5 spelling they abbreviate) at
**0**. `?` propagates ANY abrupt completion, which is `ExceptT`'s bind and
nothing else, so putting all four in `ρ` makes the correspondence
mechanical:

| the spec writes | the model writes |
| --- | --- |
| `? Foo(x)` | `← foo x` |
| `! Foo(x)` | `← foo x` at a TOTAL variant, obligation discharged |
| `UpdateEmpty(c, v)` | `updateEmpty` as a `catch` that fills an empty value |
| LabelledEvaluation's absorption | a `catch` at exactly the construct the spec names |

The alternative — `throw` in `ρ`, the other three summed into `α` — is the
Python tier's shape, and it is right THERE because `Run` predates the
substrate. Here it would make every statement's `α` a sum, force every
sequencing point to case on it, and break the one-line `?` correspondence.
`PyPost`'s flow-aware arms remain the precedent for the SPECIFICATION
layer, not for `ρ`; `docs/es-semantics-design.md` §1.2 argues both halves.
-/

namespace LeanModels.Es

/--
Why a run refused. `docs/es-charter.md` §3.6 fixes exactly three, and they
are never pooled because they retire on completely different schedules.
-/
inductive RefusalCause where
  /-- Syntax or a construct the tier does not model yet. Retires by
  climbing a rung. -/
  | unsupportedConstruct
  /-- A built-in outside the modeled slice. Retires by widening the slice,
  and is NEVER a language-tier gap — `docs/es-semantics-design.md` §3.2. -/
  | unmodeledIntrinsic
  /-- A host-defined facility: a job queue, a host hook, an
  implementation-approximated `Math`. Does not retire by building more
  language — `docs/family-architecture.md` §3.5.4 routes
  implementation-approximated here too. -/
  | environment
  deriving Repr, DecidableEq, Inhabited

/--
The base of the stack: a computation that produced a value, ran out of
fuel, or hit something the tier does not model.

These are three of `Run`'s four constructors (`LeanModels/Python/Runtime.lean`);
the fourth, `.exn`, is not here because in this tier an exception is an
ABRUPT COMPLETION and therefore lives in `ρ`, which is the whole point of
§1.2. The covenant is unchanged and is the family's: `.timeout` is fuel
exhaustion and nothing else, `.unsupported` is loud and fuel-independent.
-/
inductive Halt (α : Type) where
  | ok (value : α)
  /-- Fuel exhaustion, and nothing else. -/
  | timeout
  /-- Outside the tier. Loud, fuel-independent, and carries its cause so a
  scoreboard can bucket it without parsing prose (`docs/es-charter.md`
  §3.6: the three causes are never pooled). -/
  | unsupported (cause : RefusalCause) (message : String)
  deriving Repr, Inhabited

namespace Halt

def pure' (a : α) : Halt α := .ok a

def bind : Halt α → (α → Halt β) → Halt β
  | .ok a, f => f a
  | .timeout, _ => .timeout
  | .unsupported c m, _ => .unsupported c m

instance : Monad Halt where
  pure := pure'
  bind := bind

end Halt

/--
An abrupt completion — ES2026 §6.2.4. The four non-normal `[[Type]]`s,
each carrying what the spec's Completion Record carries for it.

`throw` carries a `Val` and NOT a closed error enum, which is this tier's
recorded requirement on the substrate's error type
(`docs/es-charter.md` §4.1, `docs/backlog.md` §L66): a thrown JS value is
an arbitrary ECMAScript language value — `language/statements/throw/S12.13_A2_T2.js`
throws a primitive — so an `Error`-shaped `ε` would be wrong about the
language. This tier is the second consumer the C charter said would settle
where such a type lives; that question is the architecture lane's and does
not block here, because the shape below is parametric in ρ.

`break`/`continue` carry an OPTIONAL target: `[[Target]]` is a label or
`empty`, and the enclosing iteration or labelled statement is what absorbs
it. Their `[[Value]]` is `empty` in the cases that arise, which is what
`UpdateEmpty` exists to fill.
-/
inductive Abrupt where
  | throw (value : Val)
  | ret (value : Val)
  | brk (target : Option String)
  | cont (target : Option String)
  deriving Repr, Inhabited

/--
The tier's semantic monad — the family's §3.4 shape, `ExceptT` OUTSIDE
`StateT` so the world survives a raise.

`W` is the world (realm, heap, execution contexts) and arrives at inch 2.
`ρ` is left a parameter rather than fixed to `Abrupt` so that the pure
fragment — the conversions of `Value.lean` — can be typed at a narrower
error type, and so the core export can replace this without a signature
change.

**Fuel is NOT in here**, per §3.4: it is an index on the step function,
because its job is to BE the recursion argument and hidden in state it is
not an argument at all.
-/
abbrev SemM (W : Type) (ρ : Type) := ExceptT ρ (StateT W Halt)

/-- The tier's usual instantiation: errors are abrupt completions. -/
abbrev EsM (W : Type) := SemM W Abrupt

namespace SemM

/-- `? Foo(x)` is `← foo x`; this is the explicit form for the rare place
a raise is written rather than propagated. -/
def raise (e : ρ) : SemM W ρ α := throw e

/-- Refuse: loud, fuel-independent, and cause-bucketed. Not an error in
`ρ` — a refusal is not something a program can catch. -/
def refuse (c : RefusalCause) (msg : String) : SemM W ρ α :=
  fun _ => Halt.unsupported c msg

/-- Fuel exhaustion. The only exhaustion outcome. -/
def timeout : SemM W ρ α := fun _ => Halt.timeout

/-- Run a computation from a world, exposing the base outcome. -/
def run (m : SemM W ρ α) (w : W) : Halt (Except ρ α × W) := m w

end SemM

namespace Abrupt

/--
`UpdateEmpty(completionRecord, value)` — ES2026 §6.2.4.6.

The spec's rule: a `return` or `throw` completion always has a value, so
it is returned unchanged; a `break`/`continue` whose `[[Value]]` is
`empty` takes the supplied one. Because `brk`/`cont` here carry no value
field at all — `empty` is the only case that arises for them in the
language core — this is currently the identity, and it is written out
rather than omitted so that the clause has a definition to cite and the
day a valued `break` is needed there is a place to put it.
-/
def updateEmpty (c : Abrupt) (_v : Val) : Abrupt := c

/-- Is this completion one an iteration statement absorbs? -/
def isLoopFlow : Abrupt → Bool
  | .brk _ | .cont _ => true
  | .throw _ | .ret _ => false

/-- Does this completion target `label`, or no label at all? An unlabelled
`break` is absorbed by the nearest iteration or switch; a labelled one
only by its own labelled statement. -/
def targets (lbl : Option String) : Abrupt → Bool
  | .brk t | .cont t => t == lbl
  | .throw _ | .ret _ => false

end Abrupt

end LeanModels.Es
