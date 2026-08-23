# The `Lean.Order` census (2026-08-23)

**The question, asked at the LEAN-CORE level.** `LeanModels/Core/Order.lean`
landed `FlatLe` — the flat approximation order the tree had written three times
(`Sv.Res.le`, `Python.Res.le`, `Monadic.PyLe`). Before that becomes furniture:
*did Lean core already have it?* Lean ≥ 4.12 ships `partial_fixpoint`, and
`partial_fixpoint` is built on a domain-theory layer. §9.0a's blind spot one
level up is exactly this — a lane censuses the tree and never the toolchain.

Measured on the pinned toolchain, `leanprover/lean4:v4.33.0-rc1`, in a
STANDALONE scratch probe with **zero project imports**, so it measures the
toolchain and nothing of any clone's build state.
`tools/check.sh` verdict: `TRUSTWORTHY: exit 0, sorry-only warnings`;
`exit code 0`, `warnings 0 total — 0 sorry, 0 other`.

## The answer: yes, and it is filed under `Init.Internal`

`Lean.Order.FlatOrder b` (`Init/Internal/Order/Basic.lean:770`) **is** `FlatLe`.
The bridge is proved, both directions:

```
FlatOrder.rel x y ↔ (x = b ∨ x = y)
```

The encodings differ in shape, not in content:

| | this tree's `FlatLe` | core's `FlatOrder` |
|---|---|---|
| carrier | the bare type | a wrapper `def FlatOrder (b : α) := α` |
| order | a `def` returning `x = bot ∨ x = y` | an `inductive rel \| bot \| refl` |
| plumbing | three theorems | `PartialOrder` + `CCPO` instances |

Core's is the more capable one: it arrives with the class machinery attached.

## What core covers of `SemMWith W ρ π σ`

`SemMWith W ρ π σ = ExceptT ρ (StateT W (Except (Loud π σ)))`.

**Every transformer is there.** `PartialOrder`, `CCPO` and `MonoBind` instances
ship for `ExceptT`, `StateT`, `ReaderT`, `OptionT` and `StateRefT'`
(`Basic.lean:914-1010`).

**The base is not, and cannot be.** Core bottoms out at `Option` (bottom
`none`) and at `IO`/`EIO`/`ST`. It has no instance for `Except ε` as a monad in
its own right, and could not: `Except ε α = ExceptT ε Id α`, so the transformer
instance would demand `PartialOrder (Id α)` for an arbitrary `α`. Our bottom is
`.error .timeout` — a CONSTRUCTOR of `Loud` in the base layer — which core has
no way to guess.

**Three instances close the gap and the whole stack then synthesises.** Twelve
lines: `PartialOrder` and `CCPO` by `inferInstanceAs (… (FlatOrder (Except.error
Loud.timeout)))` — core's own `Option` trick — and a seven-line `MonoBind` whose
two fields ARE the left and right halves of `PyLe.bind`. With those,
`example : MonoBind (SemM W ρ) := inferInstance` closes.

## What the `monotonicity` tactic does and does not discharge

The reframing is mandatory first: core's `monotone f := ∀ x y, x ⊑ y → f x ⊑ f y`
is about a function of an ORDERED DOMAIN, so `evalOpen K m e ⊑ₚ evalOpen K' m e`
has to be restated as `monotone (fun K => evalOpen K m e)`.

| shape | `monotonicity` | note |
|---|---|---|
| bind spine | **closes** | `monotone_bind` is `@[partial_fixpoint_monotone]` |
| `ite` | **closes** | `monotone_ite`, likewise |
| `tryCatch` | **not covered** | 69 tagged lemmas across the five `Order` files; `grep -c tryCatch` is 0 in all five |

`tryCatch` is not a wall: `ExceptT.tryCatch` is `bind` at the inner monad, so
the lemma is provable — and registrable.

**The seams register.** `@[partial_fixpoint_monotone]` is a documented
extension seam ("users who want to extend the `partial_fixpoint` machinery …
mark more functions as monotone or register more monads"). A `monotone_zoomIn`
written for the state-zoom adapter and tagged makes a later goal close by bare
`monotonicity`, with nothing naming the lemma. **Our seams stay ours to PROVE;
they stop being ours to DISPATCH.**

**And core's tactic is one step, not a walker.** `monotonicity`'s own docstring:
it "performs one compositional step". `partial_fixpoint` drives it. The driver
that works is `repeat' first | <leaf> | monotonicity` — the same
non-backtracking shape `mono_with` arrived at independently. That convergence is
the record's point: the walker's design was not a workaround.

## Why the tree keeps its own — the obstruction, precisely

`Kont` **can** be a core `PartialOrder`, including the obligation a bare
relation does not owe, `rel_antisymm` (flat antisymmetry + `funext` +
`Nat.le_antisymm`). That is a cost, not a barrier.

The barrier is one field down. The **pure-worker seam** — `liftRes` over a
fuel-taking trunk worker — needs `monotone (fun K => K.fuel)`, i.e. a
`Lean.Order.PartialOrder Nat` whose `rel` is `Nat.le`. Core ships none and would
not: `Nat` is no CCPO, so `partial_fixpoint` has no use for one. Five lines, and
green — but a **global orphan instance of a core class on `Nat`**, declared from
a module whose every class docstring reads *"This is intended to be used in the
construction of `partial_fixpoint`, and not meant to be used otherwise."*

## The price, and the ruling

Measured against `LeanModels/Python/Monadic/Mono.lean` (650 lines):

| | lines |
|---|---|
| removed — `PyLe` def/iff/refl, `bind_apply` + `PyLe.bind`, `PyLe.ite` | −57 |
| added — base instances (12), `Kont` antisymmetry (~9), orphan `PartialOrder Nat` (5) | +26 |
| walker shrinks — `monotonicity` replaces seven `apply` alternatives | −6 |
| unchanged in substance — `tryCatch` (34), the zooms (24), `liftRes` (10) | 68 |
| **net** | **≈ −35, about 5%** |

> **5% is not the number that decides it.** Three things are: a hard dependency
> on `Init.Internal.*` against its own stated contract (a toolchain bump can
> move it with no deprecation, and it would move under every tier at once); a
> global orphan instance on `Nat` in someone else's class; and restating all 20
> `_mono` theorems from `f K ⊑ₚ f K'` to `monotone (fun K => f K)`, which
> changes the shape the R-track consumes at its call gate.

**Ruled: adopt the idea, not the import.** `FlatLe` keeps the tree's own
spelling, and its docstring records this census so the question is answered and
dated rather than open. A separate, later spine ticket may add the three base
instances beside `FlatLe` — with a **tripwire `example` that fails loudly if
`Lean.Order.FlatOrder` moves**, so a toolchain bump is caught at the pin rather
than under every tier at once — and it restates no tier theorem.

**The law this census is an instance of:** *a shared abstraction is censused
against the TOOLCHAIN before it is censused against the tree.* The tree's three
copies were the visible duplication; core's was the fourth, and it was invisible
because nobody looked one level up.
