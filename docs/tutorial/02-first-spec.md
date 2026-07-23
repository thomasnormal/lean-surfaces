# Tutorial 02 — Your first spec

[Tutorial 01](01-first-run.md) ran a program. Now you prove one correct: the
`==>` arrow, the `py_prove` tactic, what `#py_check` buys you, and — most
important — what the theorem actually *means*.

## 1. The files

The example is the directory `Examples/python/tut_02/` in the three-file layout
of tutorial 01. The program:

```python
# Examples/python/tut_02/tut_02.py
def square(x):
    return x * x
```

`spec.lean` is the readable contract — the checks, then every theorem
*statement*, each closed by the `proofs` tactic:

```lean
-- Examples/python/tut_02/spec.lean (header comment elided)
import Examples.python.tut_02.proof

open LeanModels LeanModels.Python

load_program tut_02 from "Examples/python/tut_02/tut_02.json"

/-! Tutorial 02 (docs/tutorial/02-first-spec.md): the `==>` arrow and
`py_prove` on straight-line code. -/
#py_check tut_02.square(5) = 25
#py_check tut_02.square(-4) = 16
#py_check tut_02.square(0) = 0

/-- Total correctness: `square(x)` terminates and returns `x * x`, for
every Python int `x`. One tactic; no `Val`, no fuel, no AST in sight
(`Examples/python/tut_02/proof.lean`). -/
theorem square_total (x : PyInt) : tut_02.square(x) ==> x * x := by proofs

/-- Whatever `square(x)` returns equals `x * x` — the relational reading,
via the hypothesis-position arrow `⇓` and determinism-modulo-fuel
(`CallsTo.typed_int_eq`, Surface.lean). -/
theorem square_result (x r : PyInt) (h : tut_02.square(x) ⇓ r) : r = x * x := by proofs

/-- Squares are nonnegative — once `square_result` pins the result, the
rest is ordinary mathematics with ordinary Lean tools; the interpreter
never reappears. -/
theorem square_nonneg (x r : PyInt) (h : tut_02.square(x) ⇓ r) : 0 ≤ r := by proofs
```

The real proofs live in `proof.lean`, one theorem per spec-side statement,
same names, wrapped in the namespace matching the module path:

```lean
-- Examples/python/tut_02/proof.lean (header comment and docstrings elided)
import LeanModels

namespace Examples.python.tut_02.proof

open LeanModels LeanModels.Python

load_program tut_02 from "Examples/python/tut_02/tut_02.json"

theorem square_total (x : PyInt) : tut_02.square(x) ==> x * x := by
  py_prove [tut_02]

theorem square_result (x r : PyInt) (h : tut_02.square(x) ⇓ r) : r = x * x :=
  CallsTo.typed_int_eq h (square_total x)

theorem square_nonneg (x r : PyInt) (h : tut_02.square(x) ⇓ r) : 0 ≤ r := by
  rw [square_result x r h]
  rcases Int.le_total 0 x with hx | hx
  · exact Int.mul_nonneg hx hx
  · have := Int.mul_nonneg (a := -x) (b := -x) (by omega) (by omega)
    rwa [Int.neg_mul_neg] at this

end Examples.python.tut_02.proof
```

Two conventions to absorb once, because every example uses them. The
statements are **duplicated** between the two files — Lean has no forward
declarations — and the duplication is *typechecked*: the spec-side
`:= by proofs` resolves the same-name twin in `Examples.python.tut_02.proof` and
fails loudly if the twin is missing or its statement drifted. And the split
is uniform: `spec.lean` states, `proof.lean` proves — a reader (human or
AI) gets the whole contract from `spec.lean` without wading through
tactics.

Extract once (envelope only), then build; proof iteration afterwards is
pure Lean — edit, rebuild:

```console
$ python3 extractors/python/extract.py Examples/python/tut_02/tut_02.py
$ lake build
```

## 2. Reading the theorem

```lean
theorem square_total (x : PyInt) : tut_02.square(x) ==> x * x
```

- `x : PyInt` — theorem binders use the `Py*` brand types (`PyInt` is
  definitionally `Int`). Discipline: Python-shaped types in binders,
  mathematical Lean on the right of the arrow.
- `tut_02.square(x)` — module ident, dot, Python function name, arguments in
  parentheses. Arguments are marshalled by `ToVal` from their Lean types.
- `==> x * x` — the **total-correctness** arrow: the call *terminates* and
  returns the value on the right.

The notation is sugar with an exact meaning. `tut_02.square(x) ==> x * x`
elaborates to

```lean
-- (illustrative — the exact elaboration, see ../reference.md)
CallsTo tut_02 "square" #[ToVal.toVal x] (ToVal.toVal (x * x))
-- i.e.  ∃ fuel, callFunction tut_02 "square" #[.int x] fuel = .ok (.int (x * x))
```

"There is a fuel budget at which the definitional interpreter, run on the
literal AST of your file, returns exactly `.ok (.int (x * x))`." Since the
interpreter only ever runs *forward*, exhibiting one sufficient fuel is
termination; determinism-modulo-fuel (proved once, in
[`Obs.lean`](../../LeanModels/Python/Obs.lean)) makes the returned value
unique. The full judgment family is tabulated in
[../reference.md](../reference.md) and [../spec-surface.md](../spec-surface.md).

`py_prove [tut_02]` closes such goals for loop-free bodies: it picks a fuel
witness, symbolically executes the interpreter over the program literal
(that is why you pass `tut_02`), and discharges the residual value equation
with `rfl`/`omega`. Docstring:
[`Surface.lean`](../../LeanModels/Python/Surface.lean) (search `py_prove`).

## 3. What the theorem means — for two audiences

**Inside Lean (the formal claim).** A statement about a specific inductive
value (`tut_02 : Module`, the deep-embedded AST) and a specific computable
function (`callFunction`, the fuel-based interpreter in
[`Semantics.lean`](../../LeanModels/Python/Semantics.lean)). The kernel
checked it. There is no translation step to trust: the program was not
compiled into Lean expressions — the theorem quantifies over runs of an
interpreter you can read, on an AST you can print.

**About Python (the empirical bridge).** Two links connect that object to the
file you wrote. The AST came from CPython's own parser — parse coverage is
borrowed, not reimplemented. And the interpreter's behavior is
*differentially tested against CPython* on the shared harness (tutorial 01,
step 5): every semantic decision — floor division, bool/int coercion,
short-circuit values — is pinned by running both sides. Where the model does
not cover Python, it says so loudly (`Res.unsupported`) instead of guessing.
So the honest reading is: **proved about the model; the model is
CPython-tested on the supported tier; off-tier behavior is impossible to
state, not silently wrong.** The tier boundaries are the "v0 limitations"
list in the [README](../../README.md#v0-limitations-honest-list).

## 4. What `#py_check` buys — non-vacuity

The `#py_check` lines look redundant next to a universally quantified
theorem. They are not.

- They run *before* you prove anything. If you misspelled the function, if
  the body drifted off the supported tier, if your expectation is simply
  wrong (`square(-4)` is `16`, not `-16`), the build fails with a concrete
  witness in seconds — not after an hour of fighting an unprovable goal.
- Derived corollary forms (tutorial 04 introduces them) have the shape "*if*
  the run returns `.ok r`, then `r = …`" — universally quantified over fuel,
  and **vacuously true** if the interpreter never returns `.ok` at all. The
  concrete checks demonstrate the "if" side is inhabited. That is the house
  convention: every spec file opens with `#py_check` lines
  ([README](../../README.md), "`#py_check` non-vacuity convention").

## 5. The relational form: `⇓`

`square_result` shows the other direction of use. In hypothesis position you
write `h : tut_02.square(x) ⇓ r` — "the call returns `r`" — and conclude
things *about* `r`. It is the same judgment as `==>` (and prints back as
`==>`); the point is binding the result instead of specifying it.

How to type it: `⇓` is the judgment family's one non-ASCII symbol (`==>`,
`~~>`, `==>!` are plain ASCII). Editors with the standard Lean 4
abbreviations insert it when you type `\d=` (or `\Downarrow`) followed by a
space; outside such an editor, copy it from any example file.
`square_nonneg` then never mentions the interpreter again: once the result is
pinned, you are doing ordinary mathematics with ordinary Lean tools. This
division of labor — interpreter facts in one step, mathematics after — is
the shape of every proof in this framework.

Next: [tutorial 03](03-branching-and-preconditions.md) — branching programs,
preconditions, and how to read a goal state.

## What can go wrong

**Your spec is wrong.** State `tut_02.square(x) ==> x + x` and `py_prove`
executes the body fine, then leaves exactly the false residue (reproduced on
the current tree):

```
error: unsolved goals
x : PyInt
⊢ x * x = x + x
```

This is the failure mode you *want*: symbolic execution done, your claim
reduced to the pure equation it hinges on. Fix the spec, not the tactic.

**You forgot the program literal.** `py_prove []` cannot unfold `tut_02`
(the loaded module constant is not in the default simp set) and symbolic
execution grinds against the opaque constant until it hits the elaborator's
budget (reproduced on the current tree):

```
error: Tactic `simp` failed with a nested error:
(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

A heartbeat timeout out of `py_prove` almost always means the interpreter
could not reduce — always pass the module: `py_prove [tut_02]`. (The same
symptom appears for a wrong exception spec — [tutorial 06, bonus
modes](06-when-proofs-fail.md#bonus-quick-hits).)

**Your function has a loop.** `py_prove` is for loop-free bodies; on a loop
it leaves a goal with a frozen `execWhile … ` inside. That is not a dead end
— it is [tutorial 04](04-loops.md). (Full symptom and fix:
[tutorial 06, failure mode 1](06-when-proofs-fail.md#1-py_prove-leaves-a-goal-full-of-interpreter-noise--there-is-a-loop).)

**Precondition present, `omega` blind.** If you add a hypothesis like
`(hx : 0 ≤ x)` and `py_prove` mysteriously fails, you have hit the `PyInt`
branding gotcha — see [tutorial 03](03-branching-and-preconditions.md#3-preconditions-are-hypotheses--one-gotcha)
and [tutorial 06, failure mode 5](06-when-proofs-fail.md#5-omega-ignores-a-pyint-typed-hypothesis).
