# Spec surface — target ergonomics (normative examples)

**Status: design target, approved 2026-07-20; first slice IMPLEMENTED
(`LeanModels/Python/Surface.lean`).** Live today: `Py*` types, `ToVal`
marshalling, the `f(a, b) ==> v` / `f(a, b) ⇓ r` / `f(a, b) ==>! e` arrows
(the identifier doubles as loaded module + function name; dotted
`arith.floordiv(…)` splits), the strengthened partial arrow `f(a, b) ~~> v`
(`PartialTo` over the `Obs` spine + fuel-monotonicity, `Obs.lean`),
delaborators (`LeanModels/Python/Delab.lean`: goal states and `#check` output
print back in arrow notation, `ToVal` stripped inside judgment positions
only; `⇓` prints as `==>`; below the judgment boundary — after `unfold
CallsTo`/`obtain` — fuel and `callFunction` stay visible by design), and
`py_prove` closing straight-line *and branching* total goals
(`Examples/python/add.py`: `add(a, b) ==> a + b := by py_prove [add]`;
`my_abs` likewise), **loop proofs in clause form** via `py_begin` + `py_loop`
(`LeanModels/Python/LoopTactic.lean` — supply only `(inv := …)` and
`(dec := …)` lambdas over the loop's variables, plus `(state := […])` when a
mutated Python variable shadows a theorem binder; residual goals are
`omega`/`grind`-shaped arithmetic; see `Examples/tri/proof.lean`,
`Examples/gcd/proof.lean`, `Examples/python/sum_to.py`), and
`py_corollary [tot]` closing the standard corollary shapes
in one call. Acceptance-tested: a fresh user proved `sum_to` first-try, 8
lines vs 13 for the analogous pure-Lean proof. Not yet: `≃` /
`Py.Terminates` / contract triples, recursion automation (`py_lift` helps;
full `py_induction` deemed not worth it yet). The rest of this document
remains normative for those layers. Nothing here changes the semantics — every judgment elaborates to a
statement about the deep interpreter.

## The judgment family

| Surface | Reading | Elaborates to (sketch) |
|---|---|---|
| `f(x) ==> v` | total: terminates and returns `v` | `∃ fuel r, callFunction m "f" #[toVal x] fuel = .ok r ∧ r = toVal v` |
| `f(x) ~~> v` | partial: *if* it terminates, it returns `v` (no exception, no unsupported) | notation for the Partial contract triple over `Obs` — deliberately stronger than "if `.ok` then `v`": the bare if-returns form is vacuously provable for every `v` when the callee raises/diverges, a reward-hackable objective for an AI prover |
| `f(x) ==>! E` | terminates by raising `E` | `∃ fuel, callFunction … = .exn E` |
| `f(x) ⇓ r` | hypothesis-position: binds result `r` for relational specs | `CallsTo m "f" #[toVal x] (toVal r)` |
| `f(x) ≃ g(y)` | same outcome (value, exception, or both diverge) | outcome-equality of the two denotations |
| `Py.Terminates f(x)` | terminates somehow (value or exception) | `∃ fuel o, … ≠ timeout/unsupported` |

Conventions: preconditions are ordinary named hypotheses (`(hn : 0 ≤ n)`); binders
use `Py*` types (`PyInt` is a transparent abbrev of `Int`; `PyFloat` is a distinct
binary64 type with `toReal : PyFloat → ℝ`); marshalling via `ToVal`/`FromVal` from
source type annotations; the spec RHS is deliberately *mathematical Lean* — Python
semantics governs only the program's denotation, and the shared `Py` ops library
(`Py.floordiv = Int.fdiv`, …) is the single place operator semantics lives.
Callee specs are `@[spec]` lemmas, consumed at call sites by `py_prove [g_spec]`.

## The gallery

### 1. Warm-up — branching, total correctness

```python
# Examples/python/my_abs.py (function only)
def my_abs(x: int) -> int:
    if x < 0:
        return -x
    return x
```
```lean
@[spec] theorem my_abs_spec (x : PyInt) : my_abs(x) ==> |x|
```

### 2. Python semantics visible in the spec — floor division

```python
# Examples/python/midpoint.py (function only)
def midpoint(a: int, b: int) -> int:
    return (a + b) // 2
```
```lean
@[spec] theorem midpoint_spec (a b : PyInt) : midpoint(a, b) ==> Int.fdiv (a + b) 2

theorem midpoint_nonneg (a b : PyInt) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    midpoint(a, b) ==> (a + b) / 2
```

The general theorem must say `Int.fdiv`: Python floors, Lean's `/` truncates, and
they disagree on negatives. The prettier `/` form is honestly available only under
a sign hypothesis. This is the design working as intended — the divergence is
visible in the statement, never buried in a translation.

### 3. Partial vs. total, separated — gcd

```python
# Examples/gcd/gcd.py (the whole program — three-file layout)
def gcd(a: int, b: int) -> int:
    while b != 0:
        a, b = b, a % b
    return a
```
```lean
@[spec] theorem gcd_partial (a b : PyInt) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    gcd(a, b) ~~> Int.gcd a b
theorem gcd_total (a b : PyInt) (ha : 0 ≤ a) (hb : 0 ≤ b) : gcd(a, b) ==> Int.gcd a b

theorem gcd_abs (a b : PyInt) (h : gcd(a, b) ⇓ r) :        -- full-domain truth
    r.natAbs = Int.gcd a b
```

Partial correctness needs no termination argument; totality is a separate theorem.
The sign hypotheses on `gcd_partial` are **not** optional: Python's `%` is `fmod`,
so `gcd(4, -6)` computes `4 % -6 = -2` and returns `-2`, while `Int.gcd 4 (-6) = 2`
— the unguarded spec is *false*. (This was caught by differentially testing the
executable model against CPython before proving — which is why that step is
mandatory methodology, not hygiene.) On negatives the honest full-domain statement
is `gcd_abs`. Termination on negatives does still hold, as an optional sharpening.

### 4. Exceptions as specified behavior — first_index

```python
def first_index(xs: list, x: int) -> int:
    i = 0
    while i < len(xs):
        if xs[i] == x:
            return i
        i += 1
    raise ValueError("not found")
```
```lean
@[spec] theorem first_index_found (xs : PyList PyInt) (x : PyInt) (hmem : x ∈ xs) :
    first_index(xs, x) ==> xs.idxOf x

@[spec] theorem first_index_missing (xs : PyList PyInt) (x : PyInt) (hmem : x ∉ xs) :
    first_index(xs, x) ==>! ValueError
```

The raise is a first-class postcondition, not an error to be excluded. Lean's
`List.idxOf` *is* the least-index function — using stdlib models keeps specs
one-liners.

### 5. Relational spec via hypothesis-position `⇓` — binary_search

```python
def binary_search(xs: list, x: int) -> int:
    lo, hi = 0, len(xs) - 1
    while lo <= hi:
        mid = (lo + hi) // 2
        if xs[mid] == x:   return mid
        elif xs[mid] < x:  lo = mid + 1
        else:              hi = mid - 1
    return -1
```
```lean
theorem bs_spec (xs : PyList PyInt) (x : PyInt) (hs : xs.IsSorted)
    (h : binary_search(xs, x) ⇓ i) :
    (0 ≤ i → xs[i]! = x) ∧ (i = -1 → x ∉ xs)

theorem bs_terminates (xs : PyList PyInt) (x : PyInt) : Py.Terminates binary_search(xs, x)
```

When the postcondition isn't "equals this expression", bind the result with `⇓`
and state anything about it. `xs.IsSorted` abbreviates `xs.Pairwise (· ≤ ·)`; the
`xs[i]!` here presumes the planned Python-flavored spec-side indexing helper
(`PyInt` index, negative-index semantics) — both are spec-prelude items.

### 6. No functional model needed — sorting, relationally

```python
def insertion_sort(xs: list) -> list:
    out = []
    for x in xs:            # for-loops arrive in the next semantic tier
        out = insert(out, x)
    return out
```
```lean
theorem sort_spec (xs : PyList PyInt) (h : insertion_sort(xs) ⇓ r) :
    r.IsSorted ∧ r.Perm xs
```

### 7. Program equivalence — refactoring safety

```python
def fib_rec(n: int) -> int:
    if n < 2: return n
    return fib_rec(n - 1) + fib_rec(n - 2)

def fib_iter(n: int) -> int:
    a, b = 0, 1
    i = 0
    while i < n:
        a, b = b, a + b
        i += 1
    return a
```
```lean
theorem fib_agree (n : PyInt) : fib_rec(n) ≃ fib_iter(n)

@[spec] theorem fib_iter_spec (n : PyInt) (h : 0 ≤ n) : fib_iter(n) ==> fibModel n.toNat
```

Prove the optimized version equivalent to the naive one; spec only the naive one.

### 8. Stateable without being provable — Collatz

```python
def collatz_steps(n: int) -> int:
    steps = 0
    while n != 1:
        n = n // 2 if n % 2 == 0 else 3 * n + 1
        steps += 1
    return steps
```
```lean
theorem collatz_pow2 (k : Nat) : collatz_steps(2 ^ k) ==> k

theorem collatz_conjecture : ∀ n : PyInt, 1 ≤ n → Py.Terminates collatz_steps(n)
```

Fuel semantics makes unbounded-termination questions expressible — the framework
can state the Collatz conjecture about the actual Python program.

### 9. Composability — callee specs at call sites

```python
def dist(a: int, b: int) -> int:
    return my_abs(a - b)
```
```lean
@[spec] theorem dist_spec (a b : PyInt) : dist(a, b) ==> |a - b| := by
  py_prove [my_abs_spec]
```

The call to `my_abs` is discharged by its `@[spec]` lemma, not by re-executing its
body.

### 10. Mutation-tier preview — where arrows run out

```python
def push(stack: list, x: int) -> None:
    stack.append(x)
```
```lean
theorem push_spec (ss : List PyInt) (x : PyInt) :
    ⦃stack ↦ ss⦄ push(stack, x) ⦃_, stack ↦ ss ++ [x]⦄
```

An arrow only speaks about the return value; `push` returns `None` and its whole
meaning is the argument's new state. The mutation tier therefore needs the triple
form directly. **Decided architecture (five-way bake-off, 2026-07-20):** the
semantic spine is the observation judgment `Obs : PyCall α → PyOut → Prop` with
`PyOut ::= returns | raises | diverges | stuck` (fuel appears only inside `Obs`;
determinism and outcome-totality proved once per language; `stuck ≠ diverges` is
what keeps specs falsifiable on unsupported programs). Contract triples
`⦃P⦄ f(x) ⦃r, Q⦄ ⦃e, E⦄` over `Obs` are the canonical statement form — the only
shape covering pre/partial/total/exceptions uniformly, and the one that upgrades
to points-to slots at this tier. The arrows throughout this gallery are thin
sugar over the same spine (`==>`/`==>!` abbreviations; `~~>` = the Partial
triple). Mandatory methodology regardless of surface: every specced function
gets an executable Lean model differentially tested against CPython *before*
proving (see the gcd sign bug in example 3).

### 11. Floats — both types on stage

```python
def mean(xs: list) -> float:
    return sum(xs) / len(xs)
```
```lean
theorem mean_accuracy (xs : PyList PyFloat) (hne : xs ≠ []) (hf : ∀ x ∈ xs, x.isFinite)
    (h : mean(xs) ⇓ m) :
    |m.toReal - (xs.map (·.toReal)).sum / xs.length| ≤ mean_errBound xs
```

The program computes in `PyFloat` (binary64); the claim lives in ℝ via `toReal` —
the two-type discipline: Python types in binders and marshalling, math types only
inside spec propositions via explicit semantic maps.

## Spec-prelude shopping list (accumulated from the gallery)

- `List.IsSorted` abbrev for `Pairwise (· ≤ ·)`
- Python-flavored spec-side indexing (`PyInt` index, negative-index semantics)
- `Py.Terminates`, outcome equivalence `≃`
- `PyFloat` with `toReal`, `isFinite`, rounding lemmas (float tier)
- Error-bound combinators (`mean_errBound`-style) as the float library grows
