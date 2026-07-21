# How to derive corollary forms

Prove **one** total-correctness theorem per function; every other standard
statement shape is a determinism corollary, closed by a single
`py_corollary [tot]`. Never re-execute the body. The mechanism (two curried
determinism lemmas + a value-bridge fallback) is documented on
`py_corollary`'s docstring in
[`LeanModels/Python/Surface.lean`](../../LeanModels/Python/Surface.lean).

## The four shapes

All four, from the tree. Given `add_total (a b : PyInt) : add(a, b) ==> a + b`:

**1. Raw ∀-fuel `@[spec]` form** (the canonical DESIGN.md partial-correctness
shape — this is the one automation consumes at call sites):

```lean
-- Examples/Add.lean (generated from Examples/python/add.py)
set_option warning.simp.varHead false in
/-- `add(a, b)` returns `a + b` on int inputs: any successful run, at any
fuel, yields exactly `.int (a + b)` (partial correctness). A determinism
corollary of `add_total` — one `py_corollary` (Surface.lean). -/
@[spec] theorem add_spec (a b : Int) {fuel : Nat} {r : Val}
    (h : callFunction add "add" #[.int a, .int b] fuel = .ok r) :
    r = .int (a + b) := by
  py_corollary [add_total]
```

**2. Typed `⇓` form** (no `Val`, no fuel):

```lean
-- Examples/Tri.lean (generated from Examples/python/tri.py)
set_option warning.simp.varHead false in
/-- The typed surface form of `tri_spec`: binders are `PyInt`, the result is
bound relationally with `⇓`, and neither `Val` nor fuel appears. -/
@[spec] theorem tri_correct (n r : PyInt) (hn : 0 ≤ n) (h : tri(n) ⇓ r) :
    r = n * (n + 1) / 2 := by
  py_corollary [tri_total]
```

**3. Strengthened partial `~~>`** (free from totality via
`CallsTo.partialTo` — determinism modulo fuel):

```lean
-- Examples/Add.lean (generated from Examples/python/add.py, docstring elided)
theorem add_partial (a b : PyInt) : add(a, b) ~~> a + b := by
  py_corollary [add_total]
```

**4. Value-rewritten `==>` restatement** — same call, propositionally equal
value; pass the bridging rewrite as an extra:

```lean
-- Examples/Midpoint.lean (generated from Examples/python/midpoint.py; docstring and a linter set_option elided)
theorem midpoint_nonneg (a b : PyInt) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    midpoint(a, b) ==> (a + b) / 2 := by
  py_corollary [midpoint_spec, Int.fdiv_eq_ediv_of_nonneg]
```

Side hypotheses of `tot` (like `0 ≤ n`) are discharged by `assumption` — the
corollary must carry them too. When `tot` is indexed differently, instantiate
it in the bracket: `py_corollary [fib_total n.toNat]` (see
`Examples/python/fib.py`; the `Nat`→`Int` marshalling bridge
`Int.toNat_of_nonneg` is always included by default).

## When `@[spec]` applies — and when it does not

`@[spec]` is **not** this project's attribute: on this toolchain the name is
core Lean's `mvcgen` spec registry, which accepts Hoare-triple specifications
*and* plain (conditional) simp-shaped theorems. The full note — mechanism,
why (`register_simp_attr spec` collides at initializer time), and the
consequences — is the "`@[spec]` attribute" section at the bottom of
[`LeanModels/Python/Logic.lean`](../../LeanModels/Python/Logic.lean). Do not
paraphrase it from memory; the operational rules:

- Shapes 1 and 2 are simp-shaped (`… → r = v`) — tag them `@[spec]`.
- The arrows are ∃-fuel/∀-fuel propositions, not simp lemmas. Tagging shape
  3, 4, or the total theorem itself fails (reproduced):

  ```
  error: Invalid 'spec': target was neither a Hoare triple specification nor a 'simp' lemma
  ```

  This is why `add_total`, `gcd_total`, `midpoint_spec` etc. are *not*
  `@[spec]` — the example files note it inline.
- There is no `simp [spec]` simp set; cite registered lemmas by name
  (`py_prove [my_abs_spec]` at call sites — gallery example 9).

## What can go wrong

**The varHead warning.** Shapes 1 and 2 conclude `r = …` — a simp lemma with
a variable head. Without the `set_option` line, `@[spec]` warns (reproduced):

```
warning: Left-hand side of simp theorem has a variable as head symbol. This means the theorem will be tried on every simp step, which can be expensive. This may be acceptable for `local` or `scoped` simp lemmas.
Use `set_option warning.simp.varHead false` to disable this warning.
```

House style: silence it per-theorem with
`set_option warning.simp.varHead false in`, as in every example file.

**Missing side hypotheses.** If the corollary lacks a hypothesis `tot`
needs, the internal `assumption` fails with the leftover obligation as the
goal (reproduced — a `gcd` corollary without `ha : 0 ≤ a`):

```
error: Tactic `assumption` failed

case ha
a b : Int
…
⊢ 0 ≤ a
```

Fix: add the hypothesis to the corollary's binders.

**`omega` after a corollary, with `PyInt` binders.** (Verified.) `omega`'s
atom matching is syntactic: a fact or literal at type `PyInt` contributes
nothing, and `omega` reports `No usable constraints found` or produces a
bogus counterexample. Use `Int` binders in corollaries you finish with
`omega` — as `add_spec`/`tri_spec` do, and as
[`Examples/SidecarDemo.lean`](../../Examples/SidecarDemo.lean) demonstrates.
(`py_begin` unbrands hypotheses automatically, but only in its own flow.)

**Unbridgeable value forms.** `py_corollary`'s last resort rewrites `tot`
with `toVal_*` lemmas plus your extras under `simp (disch := omega)`. If the
two value expressions differ by real mathematics (not a rewrite you can
name), it fails — state the corollary via `have hr : r = <tot's value> := by
py_corollary [tot]` and prove the remaining equality yourself.
