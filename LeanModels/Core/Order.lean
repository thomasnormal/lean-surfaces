/-
**THE FLAT APPROXIMATION ORDER** — one definition for every fuel-bounded tier
(`docs/family-architecture.md` §3.8: a second copy arriving in a second tier is
a defect, not a design).

Every fuel-bounded interpreter in this tree orders its outcomes the same way: a
run that GAVE UP is below everything, and a run that DECIDED is below only
itself. Three in-tree orders are that shape, character for character —
`Sv.Res.le`, `Python.Res.le`, and the monadic tier's `PyLe` (pointwise) — and
they were written three times before anyone noticed they were one thing.

**WHAT THIS FILE DOES NOT DO, deliberately.** It does not re-spell the three.
Each keeps its own name, its own notation and its own ~15-20 consumers; what
lands here is the DEFINITION plus the three facts every one of them re-proves
(`refl`, `bot_le`, `eq_of_ne_bot`), and each tier states an `Iff.rfl` bridge to
this one. That is the additive shape §3.8 asks for: the tree gains a shared
name without a rename touching a single proof.

**Why `bot` is a PARAMETER rather than a class.** The bottoms are values of
unrelated types (`Res.timeout`, `Run.timeout`, `Loud.timeout` under an
`Except`), and the tiers instantiate at different universes and different
arities. A parameter costs one explicit argument at each use site and buys
nothing to keep in sync; an `OrderBot`-style class would need three instances
whose only content is naming the bottom.

**CENSUSED AGAINST THE TOOLCHAIN (2026-08-23), and core already had it.**
`Lean.Order.FlatOrder b` (`Init/Internal/Order/Basic.lean:770`) is this order,
under a different encoding: a wrapper type `def FlatOrder (b : α) := α` carrying
an inductive `rel | bot | refl`, with `PartialOrder` and `CCPO` instances. The
bridge is `FlatOrder.rel x y ↔ (x = b ∨ x = y)`, proved green.

**The tree keeps its own anyway, and the reasons are recorded rather than
assumed** — full measurement and price in
`docs/lean-order-census.md`. In short: that module is `Init.Internal`, and every
class in it says *"intended to be used in the construction of `partial_fixpoint`,
and not meant to be used otherwise"*; core's base instances stop at `Option` and
`IO`, never at our `Except (Loud π σ)`; and the monadic tier's pure-worker seam
would additionally need a GLOBAL ORPHAN `Lean.Order.PartialOrder Nat`, because
`Nat` is no CCPO and core will never ship one. The whole exchange is worth about
35 lines. A later ticket may add the three base instances *beside* this
definition — with a tripwire that fails loudly if `FlatOrder` moves — without
restating a single tier theorem.

**THE CONGRUENCES ARE NOT HERE, and that is the C-lane routing law.** `Sv.Res`
and `Python.Res` are DIFFERENT TYPES — Python's carries the `.exn` raise arm —
so `le_bind`/`le_ite` are each tier's own, over each tier's own `bind`. Lifting
them here would be the thick-trunk mistake: one lemma that has to know every
tier's monad. The order is shared; the algebra over it is not.
-/
import Init.Internal.Order.Basic

namespace LeanModels
open Lean.Order

/-- The FLAT approximation order over a designated bottom: `x` approximates `y`
iff `x` is `bot` (the computation gave up) or `x = y` (it decided, and `y`
agrees). -/
def FlatLe {α : Sort u} (bot : α) (x y : α) : Prop := x = bot ∨ x = y

/-- Reflexivity — a decided run approximates itself. -/
theorem FlatLe.refl {α : Sort u} (bot x : α) : FlatLe bot x x := Or.inr rfl

/-- `bot` is below everything. -/
theorem FlatLe.bot_le {α : Sort u} (bot y : α) : FlatLe bot bot y := Or.inl rfl

/-- **The extraction step of every `_mono` corollary**: a lower bound that is
not `bot` is already the value, so `⊑` collapses to equality. -/
theorem FlatLe.eq_of_ne_bot {α : Sort u} {bot x y : α}
    (h : FlatLe bot x y) (hx : x ≠ bot) : x = y := h.resolve_left hx


/-! ## The bridge to `Lean.Order`

The census (`docs/lean-order-census.md`) found this order already in the
toolchain. These two theorems are what make that a checked fact rather than a
remark, and the tripwire below is what makes a toolchain bump say so.

**Only the ORDER facts live here.** The base instances for the family stack
(`HaltWith`, and everything `ExceptT`/`StateT` synthesises above it) live at the
end of `Core/Outcome.lean` instead, and the reason is measured rather than
stylistic: this file is imported by `Python/Obs.lean`, `Core/Outcome.lean` is
not, and moving `Outcome` into `Obs`'s closure would drag `Std.Do`,
`Std.Tactic.Do` and the `mvcgen_trivial_extensible => grind` macro rule into all
65 `Examples/` files that import the umbrella. A shared name is worth an import;
it is not worth relocating the trunk's elaboration cost. -/

/-- `FlatLe` IS `Lean.Order.FlatOrder.rel` — the census's central claim, as a
theorem. -/
theorem FlatLe.iff_rel {α : Sort u} {b : α} (x y : α) :
    FlatLe b x y ↔ FlatOrder.rel (b := b) x y := by
  constructor
  · intro h
    rcases h with h | h
    · rw [h]; exact .bot
    · rw [h]; exact .refl
  · intro h
    cases h with
    | bot => exact Or.inl rfl
    | refl => exact Or.inr rfl

/-- And therefore it is core's `⊑` at the wrapped carrier. -/
theorem FlatLe.iff_le {α : Sort u} {b : α} (x y : α) :
    FlatLe b x y ↔ (FlatOrder.mk b x ⊑ FlatOrder.mk b y) := FlatLe.iff_rel x y

/-! ### TRIPWIRE — three `rfl`-grade facts about a module core calls INTERNAL

`Init.Internal.Order` carries no compatibility promise; its own docstrings say
it is "not meant to be used otherwise". So the shape this file depends on is
PINNED here, and a toolchain bump that changes it fails THIS file rather than
failing somewhere downstream with a confusing message. Each line names the
property it guards. -/

/-- Guards: `FlatOrder` stays a REDUCIBLE type synonym (`@[expose]`). -/
example {α : Sort u} {b : α} : FlatOrder b = α := rfl
/-- Guards: the reflexive constructor keeps its name and shape. -/
example {α : Sort u} {b : α} (x : FlatOrder b) : FlatOrder.rel x x := .refl
/-- Guards: the bottom constructor keeps its name, and `b` is still the bottom. -/
example {α : Sort u} {b : α} (x : FlatOrder b) : FlatOrder.rel b x := .bot

end LeanModels
