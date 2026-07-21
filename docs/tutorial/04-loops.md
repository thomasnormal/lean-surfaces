# Tutorial 04 — Loops

The centerpiece. A `while` loop cannot be symbolically executed away — the
number of iterations depends on the input — so *you* must supply the two
pieces of mathematical content no tactic can invent: a **loop invariant**
and a **decreasing measure**. Everything else — fuel bookkeeping, the
environment plumbing, the generic while rule — is derived for you by
`py_begin`/`py_loop` ([`LeanModels/Python/LoopTactic.lean`](../../LeanModels/Python/LoopTactic.lean);
its module docstring is the normative description of everything this
tutorial demonstrates).

This part: (a) how to *find* an invariant, (b) the clause syntax, (c) the
residual goals and how `grind`/`omega` eat them, (d) the shadowing trap and
`(state := …)`, (e) a full worked example — factorial — end to end.

## (a) Finding the invariant: run the loop by hand

Take [`tri.py`](../../Examples/python/tri.py), the triangular-number loop:

```python
# Examples/python/tri.py (function only; the full file appears in (e))
def tri(n):
    total, i = 0, 0
    while i <= n:
        total += i
        i += 1
    return total
```

Run `tri(4)` by hand and write one row **per evaluation of the loop test**
(including the final one that fails):

| test # | `total` | `i` | `i <= n`? |
|---|---|---|---|
| 1 | 0 | 0 | yes |
| 2 | 0 | 1 | yes |
| 3 | 1 | 2 | yes |
| 4 | 3 | 3 | yes |
| 5 | 6 | 4 | yes |
| 6 | 10 | 5 | **no** → return 10 |

Now interrogate the table:

1. **What stays true in every row?** `total` is always the sum
   `0 + 1 + ⋯ + (i-1)`, i.e. `total = i*(i-1)/2`. State it
   *multiplication-free* — `2*total = i*(i-1)` — because division makes
   `grind`/`omega` unhappy and the doubled form is equivalent.
2. **What ranges hold in every row?** `0 ≤ i` and `i ≤ n + 1`. The upper
   bound looks pedantic until you reach the exit: there the test gives you
   `¬(i ≤ n)`, and *only together with* `i ≤ n + 1` does that pin `i = n+1`,
   turning the invariant into `2*total = (n+1)*n` — exactly the claim. **An
   invariant without the range conjuncts strands the exit goal** (tutorial
   06, failure mode 2, shows the stuck state).
3. **Check row 1.** The invariant must hold at entry: `i = 0`, `total = 0` —
   `2*0 = 0*(0-1)` ✓, `0 ≤ 0 ≤ n+1` ✓ (needs `0 ≤ n`, hence the theorem's
   precondition).

For the measure, use the **"what does the loop have left to do"** heuristic:
count the remaining iterations. Here the loop runs while `i ≤ n`, so
`n + 1 - i` iterations remain; the measure must be `Nat`-valued, hence
`(n + 1 - i).toNat`. Check against the table: 5, 4, 3, 2, 1, 0 — strictly
decreasing while the test holds. That is all a measure has to do.

## (b) The clause syntax

```lean
-- (illustrative — the general shape; real instances follow)
py_begin [prog]
py_loop (state := [pyVar₁, pyVar₂])   -- only when names are shadowed, see (d)
        (inv := fun (v₁ v₂ : Int) => …)
        (dec := fun (v₁ v₂ : Int) => …)
```

- `py_begin [prog]` symbolically executes the function *entry* up to the
  loop and freezes there, leaving a fuel-polymorphic `hentry` in your
  context. It also restates branded binders for the arithmetic closers.
- `py_loop` consumes `hentry`, reads the loop's environment/test/body off
  it, instantiates the generic while rule
  (`execWhile_total_of_invariant`, [`Surface.lean`](../../LeanModels/Python/Surface.lean))
  with your two lambdas, discharges the interpreter obligations itself, and
  hands you back only mathematics.
- The `inv`/`dec` lambdas range over the loop's `Int` variables, and **the
  binder names must be the Python variable names** — that is how the tactic
  selects which environment slots form the logical state. Variables the body
  never mutates (like `n` in `tri`) are simply omitted.

Everything the tactic derives, the residual-goal naming scheme, and the v1
restrictions (one `while` per function, `Int` loop variables, no
`break`/`continue`/`return` in the body) are specified in the
[`LoopTactic.lean` docstring](../../LeanModels/Python/LoopTactic.lean) —
link kept short here on purpose; read it once in full.

## (c) The residual goals, and who closes them

After `py_loop` you hold four goals — **pure mathematics: no `Val`, no
fuel, no AST**. In order (shown here for factorial, captured verbatim; the
file appears in (e)):

**1. Exit algebra** — loop variables arrive *primed* (`r'`, `i'`: their
values when the loop exited), with the invariant conjuncts split as
`hinv1 hinv2 …` and the negated test as `hcont`:

```
n : Int
hn : 0 ≤ n
r' i' : Int
hcont : ¬i' ≤ n
hinv1 : 1 ≤ i'
hinv2 : i' ≤ n + 1
hinv3 : r' = factSpec (i' - 1).toNat
⊢ r' = factSpec n.toNat
```

The ritual: `hcont` + range ⇒ the exit value of the counter
(`obtain rfl : i' = n + 1 := by omega`), then the invariant *is* the claim.

**2. Invariant preservation** — unprimed variables, `hcont` now the
*positive* test, conclusion is the invariant after one body step (note the
body's effect appears already applied: `i + 1`, `r * i`):

```
⊢ 1 ≤ i + 1 ∧ i + 1 ≤ n + 1 ∧ r * i = factSpec (i + 1 - 1).toNat
```

**3. Measure decrease**:

```
⊢ (n + 1 - (i + 1)).toNat < (n + 1 - i).toNat
```

**4. Initial invariant** — at the entry values:

```
⊢ 1 ≤ 1 ∧ 1 ≤ n + 1 ∧ 1 = factSpec (1 - 1).toNat
```

Closers: `omega` for anything linear over `Int`/`Nat` (it handles `.toNat`
natively — goal 3 is a one-word `omega`); `grind` when equations must be
combined or a spec-side function unfolds (feed it the equations:
`grind [factSpec, factSpec_step]`). House pattern, visible in every example
file: one explicit bullet for the exit algebra, `all_goals grind […]` for
the rest.

## (d) The shadowing trap and `(state := …)`

Look at [`sum_to.py`](../../Examples/python/sum_to.py) — the counting-*down*
version, and the worked hard case:

```python
# Examples/python/sum_to.py (function only)
def sum_to(n: int) -> int:
    s = 0
    while n > 0:
        s += n
        n -= 1
    return s
```

The loop **mutates `n`**. Your theorem binder is also named `n` — and the
invariant must relate the running state to the *initial* `n`
(`2*s = (n - k)*(n + k + 1)` where `k` is the current countdown value).
If the lambda binder were named `n`, it would shadow the theorem's `n` and
the invariant could not mention the initial value at all.

Try the naive thing — binders `(s k)`, no escape hatch — and `py_loop`
refuses loudly (reproduced):

```
error: py_loop: loop variable `k` is not in the loop environment [n,
 s] — when the Python variable names are shadowed by ambient binders, name them with `(state := [...])`
```

`(state := [s, n])` is the fix: it names the *environment* variables
positionally, freeing the lambda binders to be anything — here `s` and `k`.
The real theorem, verbatim from the tree:

```lean
-- Examples/python/sum_to.py (lean block; builds via Examples/SumTo.lean)
theorem sum_to_total (n : PyInt) (hn : 0 ≤ n) : sum_to(n) ==> n * (n + 1) / 2 := by
  py_begin [sum_to]
  py_loop (state := [s, n])
          (inv := fun (s k : Int) => 0 ≤ k ∧ k ≤ n ∧ 2 * s = (n - k) * (n + k + 1))
          (dec := fun (s k : Int) => k.toNat)
  · obtain rfl : k' = 0 := by omega
    grind
  all_goals grind
```

Beware the **silent** version of this trap: if you name the binder `n`
anyway, `py_loop` happily matches it against the environment — and your
theorem's `n` becomes inaccessible (`n✝` in the preservation goals) while
the exit goal disconnects from the spec. Tutorial 06, failure mode 3, shows
both faces. Rule of thumb: **if the Python loop mutates a variable your
theorem also binds, you need `(state := …)`.** (Recipe form:
[../howto/handle-shadowed-loop-variables.md](../howto/handle-shadowed-loop-variables.md).)

## (e) Worked end to end

First `tri`, the loop you analyzed in (a) — theorem verbatim from
[`tri.py`](../../Examples/python/tri.py) (which also derives the
`@[spec]`/`⇓` corollary forms; see
[../howto/derive-corollary-forms.md](../howto/derive-corollary-forms.md)):

```lean
-- Examples/python/tri.py (lean block; builds via Examples/Tri.lean)
theorem tri_total (n : PyInt) (hn : 0 ≤ n) : tri(n) ==> n * (n + 1) / 2 := by
  py_begin [tri]
  py_loop (inv := fun (total i : Int) => 0 ≤ i ∧ i ≤ n + 1 ∧ 2 * total = i * (i - 1))
          (dec := fun (total i : Int) => (n + 1 - i).toNat)
  · obtain rfl : i' = n + 1 := by omega
    grind
  all_goals grind
```

Every piece is now familiar: invariant and measure from the table in (a),
no `(state := …)` because `tri` never mutates `n`, exit bullet pins
`i' = n + 1`, `grind` does the algebra (including the division step
`2*total = (n+1)*n ⇒ total = n*(n+1)/2`).

Now the exercise, solved fresh: **factorial by loop**. New wrinkle: the spec
is not a polynomial, so you write a spec-side model (`factSpec`, exactly as
[`fib.py`](../../Examples/python/fib.py) writes `fibSpec`) plus one bridge
lemma in the `Int` shape the invariant produces. Hand-run `fact(4)`
(row per test): `(r, i)` = (1,1), (1,2), (2,3), (6,4), (24,5) → exit,
return 24. In every row `r = (i-1)!` — that is the invariant; ranges
`1 ≤ i ≤ n+1`; measure `n + 1 - i` iterations left. The whole file:

```python
# Examples/python/tut_04.py
def fact(n):
    r = 1
    i = 1
    while i <= n:
        r *= i
        i += 1
    return r


# lean[
# /-! Tutorial 04 (docs/tutorial/04-loops.md): the worked exercise —
# factorial by loop, proved end-to-end with `py_begin`/`py_loop`. -/
# #py_check tut_04.fact(5) = 120
# #py_check tut_04.fact(1) = 1
# #py_check tut_04.fact(0) = 1
# #py_check tut_04.fact(-2) = 1
#
# /-- Mathematical factorial: `1, 1, 2, 6, 24, 120, …` — the spec-side
# model, `Int`-valued so it lands where the marshalled result lives. -/
# def factSpec : Nat → Int
#   | 0 => 1
#   | n + 1 => (n + 1 : Int) * factSpec n
#
# #guard factSpec 5 == 120
#
# /-- The unfolding step of `factSpec` in the exact `Int` shape the loop
# invariant produces: for `1 ≤ i`, `factSpec i.toNat` peels off one factor
# `i`. `grind` consumes this in the invariant-preservation goal. -/
# theorem factSpec_step (i : Int) (hi : 1 ≤ i) :
#     factSpec i.toNat = i * factSpec (i - 1).toNat := by
#   have h : i.toNat = (i - 1).toNat + 1 := by omega
#   rw [h, factSpec]
#   congr 1
#   omega
#
# /-- Total correctness for `n ≥ 0`: `fact(n)` terminates and returns `n!`
# — in clause form (LoopTactic.lean). Invariant: `r` holds the factorial
# of everything already multiplied in (`r = factSpec (i-1).toNat`), plus
# the range `1 ≤ i ≤ n + 1`; measure: iterations left, `(n + 1 - i)`.
# Residual goals: the exit algebra (`hcont` + range force `i' = n + 1`,
# then `hinv3` *is* the claim), and preservation/decrease/initial all fall
# to `grind` armed with `factSpec`'s equations and `factSpec_step`. -/
# theorem fact_total (n : PyInt) (hn : 0 ≤ n) : tut_04.fact(n) ==> factSpec n.toNat := by
#   py_begin [tut_04]
#   py_loop (inv := fun (r i : Int) => 1 ≤ i ∧ i ≤ n + 1 ∧ r = factSpec (i - 1).toNat)
#           (dec := fun (r i : Int) => (n + 1 - i).toNat)
#   · obtain rfl : i' = n + 1 := by omega
#     simpa using hinv3
#   all_goals grind [factSpec, factSpec_step]
#
# set_option warning.simp.varHead false in
# /-- `fact(n)` returns `n!` for `n ≥ 0`: any successful run, at any fuel,
# yields exactly `.int (factSpec n.toNat)`. A determinism corollary of
# `fact_total` — one `py_corollary` (Surface.lean). -/
# @[spec] theorem fact_spec (n : Int) (hn : 0 ≤ n) {fuel : Nat} {r : Val}
#     (h : callFunction tut_04 "fact" #[.int n] fuel = .ok r) :
#     r = .int (factSpec n.toNat) := by
#   py_corollary [fact_total]
#
# set_option warning.simp.varHead false in
# /-- The typed surface form: binders are `PyInt`, the result is bound
# relationally with `⇓`, and neither `Val` nor fuel appears. -/
# @[spec] theorem fact_correct (n r : PyInt) (hn : 0 ≤ n) (h : tut_04.fact(n) ⇓ r) :
#     r = factSpec n.toNat := by
#   py_corollary [fact_total]
# ]
```

Notes on the two non-obvious lines:

- `factSpec_step` exists because the preservation goal lives at `Int`
  (`factSpec (i + 1 - 1).toNat`) while `factSpec` recurses at `Nat`; the
  lemma is that one `toNat` unfolding, proved by `omega` twice. Writing the
  bridge lemma *in the shape the goal produces* is the general trick for
  non-polynomial specs — compare `gcd_fmod_step` in
  [`Surface.lean`](../../LeanModels/Python/Surface.lean).
- The trailing `py_corollary` theorems derive the standard corollary family
  (raw `@[spec]` form, typed `⇓` form) from `fact_total` in one call each —
  determinism modulo fuel does the work. That is
  [../howto/derive-corollary-forms.md](../howto/derive-corollary-forms.md)'s
  topic; from here on, take them as boilerplate.

**Exercise for you** (no solution in the tree — that is the point): prove
`sum of squares` — `s += i*i` — against `n*(n+1)*(2*n+1)/6`, stated
multiplication-free as `6*s = i*(i-1)*(2*i-1)`. The table method gives the
invariant in three rows.

Next: [tutorial 05](05-exceptions-and-partial.md) — exceptions and the
partial arrow.

## What can go wrong

All reproduced with real output in
[tutorial 06](06-when-proofs-fail.md); headlines here:

**Wrong/weak invariant.** Everything executes; the *exit* goal is
unprovable (`grind` fails showing `hcont` and your conjuncts, with a
concrete counterexample assignment). Missing range conjunct, nine times out
of ten. [Mode 2.](06-when-proofs-fail.md#2-wrong-invariant--the-exit-goal-is-stuck)

**Shadowed variable.** Loud error (`loop variable … is not in the loop
environment`) if your binders don't match; silently disconnected goals
(`n✝`) if they match the wrong thing.
[Mode 3.](06-when-proofs-fail.md#3-shadowed-loop-variable--state---missing)

**Clause arity.** `dec` must bind exactly `inv`'s variables (reproduced):

```
error: py_loop: `dec` must bind exactly the 2 variables of `inv`
```

**Body outside the v1 recipe.** A `return`/`break` inside the loop body (or
a non-`Int` loop variable) fails the body-step derivation (reproduced
against a scratch program with `return` in the loop):

```
error: py_loop: could not derive the body's logical step (the `hbody` obligation did not close — body shape outside the v1 recipe)
```

That is a real feature boundary, not a user error — see the v1 restrictions
in the [`LoopTactic.lean` docstring](../../LeanModels/Python/LoopTactic.lean).
