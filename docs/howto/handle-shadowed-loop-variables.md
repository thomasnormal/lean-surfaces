# How to handle shadowed loop variables

`py_loop`'s and `py_vcgen`'s `inv`/`dec` clauses are lambdas whose **binder
names select the loop variables by name** from the loop's environment. That
breaks when a theorem binder shadows the Python variable the invariant must
talk about. `py_loop` has the `(state := […])` escape hatch; `py_vcgen`
(which the migrated example files use) instead renames the *initial* values
in a private core theorem. Full mechanics: the docstrings in
[`LeanModels/Python/LoopTactic.lean`](../../LeanModels/Python/LoopTactic.lean)
and [`LeanModels/Python/VCTactic.lean`](../../LeanModels/Python/VCTactic.lean).

## When you don't need it

If no theorem binder collides with a mutated Python variable, name the
lambda binders exactly like the Python variables and omit `state`:

```lean
-- Examples/python/tri/proof.lean (three-file layout)
theorem tri_total (n : PyInt) (hn : 0 ≤ n) : tri(n) ==> n * (n + 1) / 2 := by
  py_vcgen [tri]
    (inv := fun (total i : Int) => 0 ≤ i ∧ i ≤ n + 1 ∧ 2 * total = i * (i - 1))
    (dec := fun (total i : Int) => (n + 1 - i).toNat)
  case ret =>
    obtain rfl : i' = n + 1 := by omega
    grind
  all_goals grind
```

`n` appears in the invariant, but Python's `n` is never assigned in the loop
— the theorem's `n` and the program's `n` denote the same unchanging value,
so no shadowing problem arises.

## When you do: the loop mutates a name your theorem binds

`sum_to` counts *down* by mutating `n`. The clause binders must be the
Python names `s`/`n`, and the invariant must mention the *initial* value —
so a private core renames it to `N`, and the public statement instantiates
the core (with `py_loop`, the same escape is `(state := [s, n])` plus
free binder names):

```lean
-- Examples/python/sum_to/SumTo.lean (generated from Examples/python/sum_to/sum_to.py)
private theorem sum_to_core (N : PyInt) (hN : 0 ≤ N) : sum_to(N) ==> N * (N + 1) / 2 := by
  py_vcgen [sum_to]
    (inv := fun (s n : Int) => 0 ≤ n ∧ n ≤ N ∧ 2 * s = (N - n) * (N + n + 1))
    (dec := fun (s n : Int) => n.toNat)
  case ret =>
    obtain rfl : n' = 0 := by omega
    grind
  all_goals grind

theorem sum_to_total (n : PyInt) (hn : 0 ≤ n) : sum_to(n) ==> n * (n + 1) / 2 :=
  sum_to_core n hn
```

Same situation in `gcd`, where *both* loop variables are shadowed by the
theorem binders `a b` (the invariant needs the initial values on its
right-hand side — capitalized core binders `A`/`B`):

```lean
-- Examples/python/gcd/proof.lean (three-file layout, residual bullets elided)
private theorem gcd_core (A B : PyInt) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    gcd(A, B) ==> Int.gcd A B := by
  py_vcgen [gcd]
    (inv := fun (a b : Int) => 0 ≤ a ∧ 0 ≤ b ∧ Int.gcd a b = Int.gcd A B)
    (dec := fun (a b : Int) => b.toNat)
```

Rules (`py_loop`, from its docstring):

- `(state := […])` comes **before** `(inv := …)`.
- Each entry must name a variable of the loop's environment; entries are
  matched by name, in any order.
- The i-th listed name pairs with the i-th `inv`/`dec` lambda binder.
- Residual goals display the *lambda* names — in the exit-algebra goal,
  primed (`k'`, `x'`, `y'`); invariant conjuncts split as `hinv1`, `hinv2`,
  …; the (negated/normalized) loop test is `hcont`.

## What can go wrong

**The name-capture error.** Omit `state` in `sum_to_total` and `py_loop`
reports (reproduced):

```
error: py_loop: loop variable `k` is not in the loop environment [n,
 s] — when the Python variable names are shadowed by ambient binders, name them with `(state := [...])`
```

The bracketed list is the actual loop environment (order as the interpreter
holds it), which also tells you the exact names `state` may use.

**Same error, other cause.** The message also fires when a binder is simply
misspelled (`totl` instead of `total`) — check the printed environment list
before reaching for `state`.

**`dec` arity.** The measure must bind exactly the invariant's variables
(reproduced):

```
error: py_loop: `dec` must bind exactly the 2 variables of `inv`
```

**No `hentry`.** `py_loop` before `py_begin [prog]` (reproduced):

```
error: py_loop: no `hentry` hypothesis in context — run `py_begin [<prog>]` first
```

**Out-of-recipe loops.** `py_loop`'s v1 restrictions are deliberate: one
`while` per function, `Int`-valued loop variables, no
`break`/`continue`/`return` in the body. Outside that, the tactic fails with
one of its "obligation did not close — … outside the v1 recipe" errors; fall
back to the generic while rule `execWhile_total_of_invariant` +
`py_threshold` by hand
([Surface.lean](../../LeanModels/Python/Surface.lean)).
