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

/-- A universe level that denotes `Prop` under every valuation.

The model treats levels **semantically** rather than algorithmically (there is no
`isAlwaysZero` in `VLevel`; the thesis's fourteen algorithmic order rules are
replaced by evaluation into `ℕ`), so the `Prop`-ness test is stated the same way
rather than mirroring the kernel's syntactic `isAlwaysZero`. -/
def VLevel.IsAlwaysZero (u : VLevel) : Prop := ∀ ls, u.eval ls = 0

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
  /-- The structure's type must REDUCE TO A SORT.  A stuck sort is a refusal,
  never a silent "not a `Prop`" (lean4#14807). -/
  structSortReduces : ∃ A u, env.HasType U Γ e A ∧ env.HasType U Γ A (.sort u)
  /-- Where the structure is a proposition, the projected field must be one too:
  a `Prop` structure may not yield a data field. -/
  propSquash : ∀ A u, env.HasType U Γ e A → env.HasType U Γ A (.sort u) →
    VLevel.IsAlwaysZero u →
    ∃ B w, env.HasType U Γ v B ∧ env.HasType U Γ B (.sort w) ∧ VLevel.IsAlwaysZero w

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

end LeanSurfaces
end Lean4Lean
