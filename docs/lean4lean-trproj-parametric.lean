/-
Copyright (c) 2026 lean-surfaces. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# `TrProj`, PARAMETRIC in a minimal constructor interface

`Lean4Lean/Verify/Typing/Expr.lean` declares

    def TrProj : ∀ (Γ : List VExpr) (structName : Name) (idx : Nat) (e : VExpr), VExpr → Prop := sorry

and it has been `sorry` since 2025-05-29.  It gates eleven of the twenty-one open
proof obligations in the proof layer, including the seven `TrProj.*` lemmas in
`Verify/Typing/Lemmas.lean`, which are currently statements about nothing.

## Why this file is parametric, and what the assumption is

A projection must name the *i*-th field of a structure, which needs the
structure's constructor and its arity.  **`VEnv` cannot supply that**: measured,
it has exactly two fields, `constants : Name → Option VConstant` (and
`VConstant` is `{uvars, type}` — a type and nothing more) and
`defeqs : VDefEq → Prop`.  There is no constructor table.  The only route from a
`VInductDecl` into a `VEnv` is `VEnv.addInduct`, which is itself `sorry`.

`TrProj` is therefore *downstream* of the inductive specification, which is being
written elsewhere.  Rather than invent a competing inductive interface, this file
assumes the **minimal** one — exactly what a projection consumes and nothing
more — so that the two can be reconciled by substitution.

> **ASSUMPTION TO RECONCILE.**  `ProjIface` below is an assumption, not a
> proposal about how inductives will be represented.  When the inductive
> specification lands, reconciliation is a **substitution**: replace `ProjIface`
> with the real environment lookup and re-instantiate.  Nothing in this file
> depends on how that lookup is implemented, only on what it returns, and the
> theorems below are proved for an arbitrary `ProjIface`.
-/
import Lean4Lean.Verify.Typing.Expr
-- `Theory.Typing.Basic` (reached via `Verify.Typing.Expr`) DEFINES `IsDefEq` and
-- `HasType`; their `instL` transport lemmas are PROVED here.  Without this the
-- file elaborates until it needs `VEnv.IsDefEq.instL` and then reports that the
-- environment does not contain it -- a missing import wearing a name-resolution
-- error's clothes.  Upstream's own `Verify/Typing/Lemmas.lean`, which is where
-- the seven `TrProj.*` obligations live, reaches the same module through
-- `Theory.Typing.Strong`.  No cycle: `Theory/` never imports `Verify/`.
import Lean4Lean.Theory.Typing.Lemmas

namespace Lean4Lean
namespace LeanSurfaces

open Lean (Name)

/-- The MINIMAL constructor interface a projection consumes: how many arguments
of a constructor application precede the fields, and how many fields there are.

Deliberately *not* included, because `TrProj` does not consume them: the
constructor's name, its type, the universe parameters, the inductive's indices.
Anything more would be a guess about `addInduct`'s representation. -/
structure ProjIface where
  /-- Arguments before the fields (the structure's parameters). -/
  nparams : Name → Nat
  /-- Number of fields of the structure's single constructor. -/
  nfields : Name → Nat

/-- A level that denotes `Prop` under EVERY valuation — the model's semantic
reading of the kernel's `isAlwaysZero`.

The model treats levels semantically rather than algorithmically (the thesis's
fourteen algorithmic order rules are replaced by evaluation into `ℕ`), so both
level predicates here are stated by evaluation rather than syntactically. -/
def VLevel.IsAlwaysZero (u : VLevel) : Prop := ∀ ns, u.eval ns = 0

/-- A level that denotes `Prop` under SOME valuation — the model's reading of the
kernel's `!isNeverZero`, which is what `inferProj` actually tests
(`maybePropType := !(← getSortLevel type).isNeverZero`).

**The polarity here is load-bearing and was got wrong first.**  Requiring the
structure's sort to be `Prop` *always* is unsound: `instL` can turn `Type u` into
`Prop` by taking `u := 0`, so a structure that is not a proposition at one
instantiation can become one at another, and a data field projected out of it
then yields `False`.  The arena tests that family as `proj-of-imax-prop`, and the
official kernel failed it at v4.28.0.

It is also what makes the transport lemmas go through, in both directions and for
the same reason they are true: `MaybeZero` transports *backwards* along `instL`
(§`MaybeZero.of_inst`) so it can discharge a hypothesis, while `IsAlwaysZero`
transports *forwards* (§`IsAlwaysZero.inst`) so it can supply a conclusion. -/
def VLevel.MaybeZero (u : VLevel) : Prop := ∃ ns, u.eval ns = 0

/-- `IsAlwaysZero` survives level instantiation: a field that is a proposition
stays one. -/
theorem VLevel.IsAlwaysZero.inst {u : VLevel} {ls : List VLevel}
    (h : VLevel.IsAlwaysZero u) : VLevel.IsAlwaysZero (u.inst ls) := by
  intro ns; rw [VLevel.eval_inst]; exact h _

/-- `MaybeZero` REFLECTS along level instantiation: if the instantiated sort can
be `Prop`, the original could too — the witness is the instantiated valuation.
This is the direction the side condition needs, and the reason the structure side
must be `MaybeZero` rather than `IsAlwaysZero`. -/
theorem VLevel.MaybeZero.of_inst {u : VLevel} {ls : List VLevel}
    (h : VLevel.MaybeZero (u.inst ls)) : VLevel.MaybeZero u := by
  obtain ⟨ns, hns⟩ := h; exact ⟨ls.map (VLevel.eval ns), by rwa [VLevel.eval_inst] at hns⟩

/-- `ArgFromRight k e v` : peeling `k` applications off the spine of `e` exposes
an application whose argument is `v`.

Indexing from the right is not a convenience — it is what `VExpr`'s binary `.app`
spine gives directly, and it is why every lemma in §"structural lemmas" below is
a one-line induction: `lift`, `inst` and `instL` all distribute over `.app`, so
they commute with this relation definitionally. -/
inductive ArgFromRight : Nat → VExpr → VExpr → Prop
  | zero {f v} : ArgFromRight 0 (.app f v) v
  | succ {k f a v} : ArgFromRight k f v → ArgFromRight (k + 1) (.app f a) v

/-- The COMPUTATIONAL half: `v` is the `idx`-th field of the constructor
application `e`.

This mirrors lean4lean's own `reduceProjCore`, which selects
`args[numParams + idx]` from a constructor application; counted from the right of
a `nparams + nfields` spine that is `nfields - 1 - idx`. -/
def ProjField (PI : ProjIface) (S : Name) (idx : Nat) (e v : VExpr) : Prop :=
  ArgFromRight (PI.nfields S - 1 - idx) e v

/-- The SOUND SIDE CONDITION, and it is this definition's centre.

**This is the part that is novel and representation-independent**, and it is
stated to match the *sound* rule rather than the reference kernel's behaviour.

Witnesses, recorded because the rule was chosen against an implementation that
gets it wrong: the Lean Kernel Arena's `proj-of-stuck-prop` and
`proj-of-subst-prop` are proofs of `False` accepted by the official C++ kernel at
v4.28.0, v4.29.1, **v4.33.0 (our pin)** and nightly-2026-08-01.  The arena's
mechanism note isolates two independent defects, fixed upstream separately:

* `leanprover/lean4#14807` — the projection half.  The kernel's `is_prop` test
  did not require the inferred type to **reduce to a sort**, so a *stuck* sort
  read as "not a `Prop`" and a data field was projected out of a proposition.
* `leanprover/lean4#14806` — the defeq-cache half (hash-gated transitivity).
  `proj-of-subst-prop` reaches the same projection **without** the cache, which
  is why the projection defect stands on its own.

`structSortReduces` is the first fix stated in the model: the structure's type
must *have* a sort, not merely fail to be observed as `Prop`.  lean4lean's
executable checker already enforces this — `getSortLevel` routes through
`ensureSortCore`, which `whnf`s and then **throws** `.typeExpected` rather than
returning "not a sort" — which is why that checker rejects all four arena
projection tests while our pinned kernel accepts them. -/
structure ProjSound (env : VEnv) (U : Nat) (Γ : List VExpr) (e v : VExpr) : Prop where
  /-- The structure's type must REDUCE TO A SORT — stated here as: it HAS a type
  which HAS a sort.  A stuck sort is a refusal, never a silent "not a `Prop`"
  (lean4#14807).  And where that sort could be `Prop` under any valuation, the
  projected field must be a proposition under every valuation.

  **Stated existentially, deliberately.**  A `∀ A u, … → …` shape does not
  transport along `instL` (nothing reflects an arbitrary instantiated type back
  to an uninstantiated one), so it could not be validated by the lemmas below.
  The `∃` shape is also the idiom the model already uses — `IsType` is
  `∃ u, HasType Γ A (.sort u)`. -/
  sound : ∃ A u B w,
    env.HasType U Γ e A ∧ env.HasType U Γ A (.sort u) ∧
    env.HasType U Γ v B ∧ env.HasType U Γ B (.sort w) ∧
    (VLevel.MaybeZero u → VLevel.IsAlwaysZero w)

/-- The parametric `TrProj`.

Substituting a real environment lookup for `PI` — and dropping `env`/`U`, which
the declaration site in `Expr.lean` does not currently carry — is the whole of
the reconciliation. -/
def TrProjP (PI : ProjIface) (env : VEnv) (U : Nat)
    (Γ : List VExpr) (S : Name) (idx : Nat) (e v : VExpr) : Prop :=
  ProjField PI S idx e v ∧ ProjSound env U Γ e v

/-! ## Structural lemmas

The seven open `TrProj.*` obligations are all *structural* — they say the
relation commutes with lifting, instantiation and level instantiation, and that
it is functional up to definitional equality.  None of them needs the constructor
table, which is why they can be validated against the parametric definition
before the reconciliation happens. -/

/-- `ArgFromRight` is FUNCTIONAL: the same index into the same spine gives the
same argument.  This is the computational half of `TrProj.uniq`, and it holds
outright rather than up to definitional equality. -/
theorem ArgFromRight.det : ∀ {k e v v'}, ArgFromRight k e v → ArgFromRight k e v' → v = v'
  | _, _, _, _, .zero, .zero => rfl
  | _, _, _, _, .succ h, .succ h' => ArgFromRight.det h h'

/-- `ProjField` is functional — the validation lemma for the computational half.
Its consumer is `TrProj.uniq`. -/
theorem ProjField.det {PI S idx e v v'}
    (h : ProjField PI S idx e v) (h' : ProjField PI S idx e v') : v = v' :=
  ArgFromRight.det h h'

/-! ### The relational validation lemma: `instL`

`TrProj.instL` is the cheapest of the seven open obligations against this
definition, and it is proved here for the parametric form.  Upstream it reads

    theorem TrProj.instL (H : TrProj Γ s i e e') :
      TrProj (Γ.map (VExpr.instL ls)) s i (e.instL ls) (e'.instL ls)

Both halves go through, and for structural reasons rather than by luck: `instL`
distributes over `.app` **without touching binder depth**, so the spine relation
commutes definitionally; and the level side transports because the two
predicates were given the polarities the kernel actually uses. -/

/-- The spine relation commutes with level instantiation.  One line per
constructor: `VExpr.instL` maps `.app f a` to `.app f.instL a.instL`, so both
cases are definitional. -/
theorem ArgFromRight.instL {ls : List VLevel} :
    ∀ {k e v}, ArgFromRight k e v → ArgFromRight k (e.instL ls) (v.instL ls)
  | _, _, _, .zero => .zero
  | _, _, _, .succ h => .succ (ArgFromRight.instL h)

/-- The computational half commutes with level instantiation. -/
theorem ProjField.instL {PI S idx e v} {ls : List VLevel}
    (H : ProjField PI S idx e v) : ProjField PI S idx (e.instL ls) (v.instL ls) :=
  ArgFromRight.instL H

/-- The SOUND half commutes with level instantiation.

This is where the polarity of §`VLevel.MaybeZero` earns itself: the hypothesis
`MaybeZero (u.inst ls)` is discharged by reflecting it back with
`MaybeZero.of_inst`, and the conclusion `IsAlwaysZero w` is transported forward
with `IsAlwaysZero.inst`.  With `IsAlwaysZero` on the structure side the first
step is simply false, which is how the definition's original polarity defect was
found. -/
theorem ProjSound.instL {env : VEnv} {U U' : Nat} {Γ : List VExpr} {e v : VExpr}
    {ls : List VLevel} (hls : ∀ l ∈ ls, l.WF U') (H : ProjSound env U Γ e v) :
    ProjSound env U' (Γ.map (VExpr.instL ls)) (e.instL ls) (v.instL ls) := by
  obtain ⟨A, u, B, w, hA, hu, hB, hw, himp⟩ := H.sound
  exact ⟨A.instL ls, u.inst ls, B.instL ls, w.inst ls,
    hA.instL hls, hu.instL hls, hB.instL hls, hw.instL hls,
    fun h0 => (himp h0.of_inst).inst⟩

/-! ### `wf` — the fourth obligation, and the reason the structure above was restructured

`TrProj.wf` concludes `VExpr.WF env U Γ e'`, and `VExpr.WF` unfolds to
`IsDefEqU U Γ e e` — *"the field has a type"*.  The first version of `ProjSound`
typed the field only INSIDE the `Prop` case, so when the structure's sort was not
maybe-`Prop` the definition said nothing whatever about `v`, and `wf` was simply
underivable.  Hoisting the typing out of the implication — leaving the
`Prop`-squash as a condition on the LEVELS alone — makes the definition strictly
stronger, says exactly the same thing about soundness, and transports
identically.

Upstream's statement also takes `(H2 : VExpr.WF env U Γ e)`.  This version does
not need it: `ProjSound` already carries the structure's typing, so the
hypothesis is redundant here and is omitted rather than accepted and ignored. -/

/-- The projected field is well-formed — unconditionally. -/
theorem ProjSound.wf {env : VEnv} {U : Nat} {Γ : List VExpr} {e v : VExpr}
    (H : ProjSound env U Γ e v) : VExpr.WF env U Γ v :=
  let ⟨_, _, B, _, _, _, hB, _, _⟩ := H.sound; ⟨B, hB⟩

/-- **THE FOURTH VALIDATION LEMMA.**  `TrProj.wf` for the parametric form. -/
theorem TrProjP.wf {PI : ProjIface} {env : VEnv} {U : Nat} {Γ : List VExpr}
    {S : Name} {idx : Nat} {e v : VExpr}
    (H : TrProjP PI env U Γ S idx e v) : VExpr.WF env U Γ v :=
  H.2.wf

/-! ### `instN` — the second obligation

`inst` leaves sorts inert (`.sort u, _, _ => .sort u`), so unlike `instL` the
level predicates need no transport here: the SAME `u` and `w` are reused. The
spine argument is identical, because `.app` instantiates both subterms at the
same depth `k` — only `lam`/`forallE` step to `k+1`.

**One trap, recorded because it is invisible at the call site.**
`VEnv.HasType.instN` takes `(henv) (W) (H) (h₀)` while `VEnv.IsDefEq.instN` takes
`(henv) (h₀) (W) (H)`. `HasType` is a `def` that unfolds to `IsDefEq`, so DOT
NOTATION on a `HasType` hypothesis resolves to the `IsDefEq` lemma and silently
mis-slots the arguments. (`instL` above is safe only by luck: its two orders
agree.) Every use below therefore names `VEnv.HasType.instN` explicitly. -/

/-- The spine relation commutes with instantiation, at any depth. -/
theorem ArgFromRight.instN {e₀ : VExpr} {k : Nat} :
    ∀ {n e v}, ArgFromRight n e v → ArgFromRight n (e.inst e₀ k) (v.inst e₀ k)
  | _, _, _, .zero => .zero
  | _, _, _, .succ h => .succ (ArgFromRight.instN h)

/-- The computational half commutes with instantiation. -/
theorem ProjField.instN {PI S idx e v} {e₀ : VExpr} {k : Nat}
    (H : ProjField PI S idx e v) : ProjField PI S idx (e.inst e₀ k) (v.inst e₀ k) :=
  ArgFromRight.instN H

/-- The sound half commutes with instantiation.

The sorts are carried through UNCHANGED — `inst` does not touch `.sort` — so the
`MaybeZero`/`IsAlwaysZero` obligations transfer without any level lemma. -/
theorem ProjSound.instN {env : VEnv} {U : Nat} {Γ₀ Γ₁ Γ : List VExpr}
    {e₀ A₀ : VExpr} {k : Nat} {e v : VExpr}
    (henv : env.Ordered) (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (h₀ : env.HasType U Γ₀ e₀ A₀) (H : ProjSound env U Γ₁ e v) :
    ProjSound env U Γ (e.inst e₀ k) (v.inst e₀ k) := by
  obtain ⟨A, u, B, w, hA, hu, hB, hw, himp⟩ := H.sound
  exact ⟨A.inst e₀ k, u, B.inst e₀ k, w,
    VEnv.HasType.instN henv W hA h₀, VEnv.HasType.instN henv W hu h₀,
    VEnv.HasType.instN henv W hB h₀, VEnv.HasType.instN henv W hw h₀, himp⟩

/-! ### `weak'` — the third obligation

Structurally identical to `instN`: `lift'` distributes over `.app` at the SAME
`Lift` (`| .app fn arg, k => .app (fn.lift' k) (arg.lift' k)`; only `lam` and
`forallE` step to `k.cons`), and sorts are inert (`| .sort u, _ => .sort u`), so
again no level transport is needed and the same `u`, `w` carry through.

**The argument-order trap does NOT fire here** — `VEnv.IsDefEq.weak'` and
`VEnv.HasType.weak'` both take `(henv) (W) (H)`. The lemma is still named
explicitly: the rule is not to depend on two orders happening to agree, which is
exactly the luck `instL` was relying on. -/

/-- The spine relation commutes with lifting. -/
theorem ArgFromRight.weak' {l : Lift} :
    ∀ {n e v}, ArgFromRight n e v → ArgFromRight n (e.lift' l) (v.lift' l)
  | _, _, _, .zero => .zero
  | _, _, _, .succ h => .succ (ArgFromRight.weak' h)

/-- The computational half commutes with lifting. -/
theorem ProjField.weak' {PI : ProjIface} {S : Name} {idx : Nat} {e v : VExpr} {l : Lift}
    (H : ProjField PI S idx e v) : ProjField PI S idx (e.lift' l) (v.lift' l) :=
  ArgFromRight.weak' H

/-- The sound half commutes with lifting.  Sorts are inert under `lift'`, so the
`MaybeZero`/`IsAlwaysZero` obligations transfer with no level lemma. -/
theorem ProjSound.weak' {env : VEnv} {U : Nat} {Γ Γ' : List VExpr} {l : Lift} {e v : VExpr}
    (henv : env.Ordered) (W : Ctx.Lift' l Γ Γ') (H : ProjSound env U Γ e v) :
    ProjSound env U Γ' (e.lift' l) (v.lift' l) := by
  obtain ⟨A, u, B, w, hA, hu, hB, hw, himp⟩ := H.sound
  exact ⟨A.lift' l, u, B.lift' l, w,
    VEnv.HasType.weak' henv W hA, VEnv.HasType.weak' henv W hu,
    VEnv.HasType.weak' henv W hB, VEnv.HasType.weak' henv W hw, himp⟩

/-- **THE THIRD VALIDATION LEMMA.**  `TrProj.weak'` for the parametric form. -/
theorem TrProjP.weak' {PI : ProjIface} {env : VEnv} {U : Nat} {Γ Γ' : List VExpr}
    {S : Name} {idx : Nat} {l : Lift} {e v : VExpr}
    (henv : env.Ordered) (W : Ctx.Lift' l Γ Γ') (H : TrProjP PI env U Γ S idx e v) :
    TrProjP PI env U Γ' S idx (e.lift' l) (v.lift' l) :=
  ⟨ProjField.weak' H.1, ProjSound.weak' henv W H.2⟩

/-- **THE SECOND VALIDATION LEMMA.**  `TrProj.instN` for the parametric form. -/
theorem TrProjP.instN {PI : ProjIface} {env : VEnv} {U : Nat} {Γ₀ Γ₁ Γ : List VExpr}
    {S : Name} {idx : Nat} {e₀ A₀ : VExpr} {k : Nat} {e v : VExpr}
    (henv : env.Ordered) (W : Ctx.InstN Γ₀ e₀ A₀ k Γ₁ Γ)
    (h₀ : env.HasType U Γ₀ e₀ A₀) (H : TrProjP PI env U Γ₁ S idx e v) :
    TrProjP PI env U Γ S idx (e.inst e₀ k) (v.inst e₀ k) :=
  ⟨ProjField.instN H.1, ProjSound.instN henv W h₀ H.2⟩

/-- **THE VALIDATION LEMMA.**  `TrProj.instL` for the parametric definition —
the cheapest of the seven obligations that `TrProj`'s absence had left as
statements about nothing. -/
theorem TrProjP.instL {PI : ProjIface} {env : VEnv} {U U' : Nat} {Γ : List VExpr}
    {S : Name} {idx : Nat} {e v : VExpr} {ls : List VLevel}
    (hls : ∀ l ∈ ls, l.WF U') (H : TrProjP PI env U Γ S idx e v) :
    TrProjP PI env U' (Γ.map (VExpr.instL ls)) S idx (e.instL ls) (v.instL ls) :=
  ⟨H.1.instL, H.2.instL hls⟩

end LeanSurfaces
end Lean4Lean
