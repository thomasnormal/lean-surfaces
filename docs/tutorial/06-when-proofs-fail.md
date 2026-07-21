# Tutorial 06 — When proofs fail

Every error below was reproduced against the current tree (scratch files
under `/tmp`, programs from `Examples/python/`), and every quoted message is
pasted, not paraphrased. Format: **symptom → diagnosis → fix**. The fixed
versions live in [`tut_06.py`](../../Examples/python/tut_06.py):

```python
# Examples/python/tut_06.py
def count_up(n):
    i = 0
    while i < n:
        i += 1
    return i


def true_div(a, b):
    return a / b


# lean[
# /-! Tutorial 06 (docs/tutorial/06-when-proofs-fail.md): the *fixed*
# versions of that tutorial's failure walkthroughs. Every broken variant
# shown in the tutorial was reproduced against exactly this program. -/
# #py_check tut_06.count_up(5) = 5
# #py_check tut_06.count_up(0) = 0
#
# /-- Failure modes 1 and 2, fixed: `count_up` has a loop, so `py_prove`
# cannot close it — `py_begin`/`py_loop` with the *right* invariant can.
# The invariant needs both the range conjuncts: dropping `i ≤ n` strands
# the exit goal (tutorial 06 shows the stuck state). -/
# theorem count_up_total (n : PyInt) (hn : 0 ≤ n) : tut_06.count_up(n) ==> n := by
#   py_begin [tut_06]
#   py_loop (inv := fun (i : Int) => 0 ≤ i ∧ i ≤ n)
#           (dec := fun (i : Int) => (n - i).toNat)
#   all_goals grind
#
# /-! Failure mode 6: `a / b` is true division — a float, outside the v0
# semantic tier. The interpreter refuses *loudly* (`Res.unsupported`,
# never a wrong value); `unsupported` has no surface arrow on purpose, so
# the check stays a raw `#guard … matches`. -/
# #guard (callFunction tut_06 "true_div" #[.int 7, .int 2] 100 matches .unsupported _)
# ]
```

## 1. py_prove leaves a goal full of interpreter noise — there is a loop

**Symptom.** You wrote (illustrative — the broken variant):

```lean
-- (illustrative — broken)
theorem count_up_total (n : PyInt) (hn : 0 ≤ n) : tut_06.count_up(n) ==> n := by
  py_prove [tut_06]
```

and got 78 lines of unsolved goal, beginning:

```
error: unsolved goals
n : PyInt
hn : 0 ≤ n
⊢ ∃ a b,
    (∃ a_1 b_1,
        execWhile
              {
                functions :=
                  #[{ name := "count_up",
                      params := …
```

(elided — the rest is your program's full AST and the interpreter state).

**Diagnosis.** The giveaway is the frozen **`execWhile`** application:
symbolic execution ran the entry, hit the loop, and stopped — `py_prove`
has no invariant to offer, and a loop cannot be executed away for symbolic
`n`. This is a feature: recursion points stay frozen rather than unrolling
forever.

**Fix.** The loop tactics, with the two clauses only you can supply
([tutorial 04](04-loops.md)) — the working proof is `count_up_total` in
`tut_06.py` above.

## 2. Wrong invariant — the exit goal is stuck

**Symptom.** Same theorem, loop tactic used, but the invariant dropped the
upper bound (`0 ≤ i` instead of `0 ≤ i ∧ i ≤ n`). Everything runs;
`all_goals grind` then fails on the *first* residual goal:

```
error: `grind` failed
case grind
n : Int
hn : 0 ≤ n
i' : Int
hinv : 0 ≤ i'
hcont : ¬i' < n
h : ¬i' = n
⊢ False
[grind] Goal diagnostics
  [facts] Asserted facts
    [prop] -1 * n ≤ 0
    [prop] -1 * i' ≤ 0
    [prop] n + -1 * i' ≤ 0
    [prop] ¬i' = n
  …
  [cutsat] Assignment satisfying linear constraints
    [assign] n := 0
    [assign] i' := 1
```

**Diagnosis.** Read the stuck state like this: primed variables (`i'`) mean
you are at the **exit**; `hcont : ¬i' < n` is the failed loop test; `hinv`
is everything your invariant gave you. The goal (after grind's negation)
demands `i' = n`, but `hcont` + `hinv` only give `n ≤ i'` — and grind even
hands you the counterexample it found: `n := 0, i' := 1`. Your invariant
admits states the loop can never reach; the missing fact is exactly the
absent conjunct `i ≤ n`.

**Fix.** Return to the hand-run table ([tutorial
04 (a)](04-loops.md#a-finding-the-invariant-run-the-loop-by-hand)): range
conjuncts are part of the invariant. With `0 ≤ i ∧ i ≤ n`, the exit has
`¬ i' < n` and `i' ≤ n`, so `i' = n` — done.

## 3. Shadowed loop variable — (state := …) missing

**Symptom** (the loud face). On
[`sum_to.py`](../../Examples/python/sum_to.py), lambda binders `(s k)`
without the escape hatch:

```
error: py_loop: loop variable `k` is not in the loop environment [n,
 s] — when the Python variable names are shadowed by ambient binders, name them with `(state := [...])`
```

**Symptom** (the silent face). Rename the binder to `n` so it *does* match
the environment — the tactic proceeds, and you land in unprovable goals: an
exit goal whose invariant facts never mention the spec —

```
n : Int
hn : 0 ≤ n
s' n' : Int
hcont : ¬0 < n'
hinv1 : 0 ≤ n'
hinv2 : 2 * s' = 0
⊢ s' = n * (n + 1) / 2
```

— and preservation goals where your theorem's `n` has become the
inaccessible `n✝` (the lambda binder shadowed it):

```
case hinv
n✝ : Int
hn : 0 ≤ n✝
s n : Int
hcont : 0 < n
```

**Diagnosis.** The Python loop mutates `n`; your theorem also binds `n`; the
invariant must relate the running value to the *initial* one, and a binder
named `n` makes the initial one unnameable. The dagger `n✝` in a residual
goal is the tell.

**Fix.** `(state := [s, n])` names the environment slots positionally,
freeing the binders (`fun (s k : Int) => …`). Worked case:
[tutorial 04 (d)](04-loops.md#d-the-shadowing-trap-and-state--); recipe:
[../howto/handle-shadowed-loop-variables.md](../howto/handle-shadowed-loop-variables.md).

## 4. A #py_check fails — three different diseases, one symptom

**Symptom.** All three of these (illustrative — broken variants of real
checks) fail the build with the *same-shaped* message:

```lean
-- (illustrative — broken)
#py_check tut_01.double(21) = 43        -- value simply wrong
#py_check tut_06.count_up(5000) = 5000  -- fuel too small (fixed 4096)
#py_check tut_06.true_div(7, 2) = 3     -- unsupported construct
```

```
error: Expression
  callFunction tut_01 "double" #[ToVal.toVal 21] 4096 == Res.ok (ToVal.toVal 43)
did not evaluate to `true`
error: Expression
  callFunction tut_06 "count_up" #[ToVal.toVal 5000] 4096 == Res.ok (ToVal.toVal 5000)
did not evaluate to `true`
error: Expression
  callFunction tut_06 "true_div" #[ToVal.toVal 7, ToVal.toVal 2] 4096 == Res.ok (ToVal.toVal 3)
did not evaluate to `true`
```

**Diagnosis.** One `#eval` per failing check tells them apart (real output):

```lean
-- (illustrative — diagnosis snippet, delete after use)
#eval callFunction tut_01 "double" #[.int 21] 4096
#eval callFunction tut_06 "count_up" #[.int 5000] 4096
#eval callFunction tut_06 "true_div" #[.int 7, .int 2] 4096
```

```
LeanModels.Python.Res.ok (LeanModels.Python.Val.int 42)
LeanModels.Python.Res.timeout
LeanModels.Python.Res.unsupported "unsupported expression 'BinOp:Div'"
```

**Fix**, per disease: `.ok` with a different value — your expectation is
wrong, fix the number (or discover your function is wrong: that is the check
working). `.timeout` — the run needs more than `#py_check`'s fixed fuel of
4096; use a smaller input, or a raw
`#guard callFunction … 100000 == .ok …` (at fuel 100000 the `count_up(5000)`
run really does return `.ok (.int 5000)` — concrete runs cost time
proportional to steps taken, not fuel given). `.unsupported` — see mode 6.

## 5. omega ignores a PyInt-typed hypothesis

**Symptom.** A blatantly true arithmetic goal fails (reproduced):

```lean
-- (illustrative — broken)
example (x : PyInt) (hx : 0 ≤ x) : 0 ≤ x + 1 := by omega
```

```
error: omega could not prove the goal:
No usable constraints found. You may need to unfold definitions so `omega` can
see linear arithmetic facts about `Nat` and `Int`, which may also involve
multiplication, division, and modular remainder by constants.
```

The same root cause makes `py_prove` fail on branching goals that need a
precondition (its closer is `omega` — tutorial 03's `relu_of_nonneg`), and
makes an `omega` bullet after `py_loop` unable to use a theorem-level
hypothesis like `hn : 0 ≤ n` even though residual-goal facts (`hcont`,
`hinv*`) work fine.

**Diagnosis.** `PyInt` is *definitionally* `Int`, but a hypothesis stated
over a `PyInt` binder is elaborated with `PyInt`-headed instances
(`@LE.le PyInt …`), and `omega`'s atom matching is syntactic — it does not
unfold the brand, so the hypothesis contributes nothing ("No usable
constraints found"). Facts produced *by the tactics* (split hypotheses,
`hcont`, `hinv*`) are built at `Int` and unaffected. `grind` is also
unaffected (it sees through reducible abbreviations) — which is why the
house style closes loop residuals with `grind`, and why this bites mostly
around `py_prove` and hand-written `omega` bullets.

**Fix.** Restate the hypothesis at `Int` — one line, before the tactic that
needs it:

```lean
have hx' : (0 : Int) ≤ x := hx
```

Real instance: `relu_of_nonneg` in
[`tut_03.py`](../../Examples/python/tut_03.py). Alternatively close with
`grind` instead of `omega` where that fits the goal.

## 6. The loud `.unsupported` — you left the semantic tier

**Symptom.** Any of: a `#py_check` fails and the `#eval` diagnosis of mode 4
shows

```
LeanModels.Python.Res.unsupported "unsupported expression 'BinOp:Div'"
```

or the runner says

```console
$ lake exe leanmodels-run Examples/python/tut_06.json true_div 7 2
{"status":"unsupported","msg":"unsupported expression 'BinOp:Div'"}
```

**Diagnosis.** This is not an error in your proof and not a Python
exception: the construct (here true division `/`, which is float-valued) is
**representable but outside the v0 semantic tier**. The interpreter refuses
loudly rather than approximating — `Res.unsupported` is a distinct outcome,
it propagates like an exception through the run, and *no arrow can state
it*: you cannot accidentally prove anything about an off-tier program (a
`~~>` spec is refutable against it, mode 4 of the
[`Surface.lean`](../../LeanModels/Python/Surface.lean) `PartialTo.iff_obs`
docstring — the `stuck` outcome). The message names the construct
(`'BinOp:Div'`); the tier boundary is the "v0 limitations" list in the
[README](../../README.md#v0-limitations-honest-list) and the supported-tier
table in [../DESIGN.md](../DESIGN.md). Check what the extractor kept vs
flagged: [../howto/check-what-the-extractor-supports.md](../howto/check-what-the-extractor-supports.md).

**Fix.** Stay on the tier (rewrite `a / b` as `a // b` if integer division
was meant), or record the gap honestly: keep the function, assert the
refusal (`#guard … matches .unsupported _`, as `tut_06.py` does), and
whitelist it in the harness with `"expect": "unsupported"`
([`harness/cases.json`](../../harness/cases.json) does exactly this for
`true_div`).

## Bonus quick hits

All reproduced; one line each.

**`py_loop` without `py_begin`:**

```
error: py_loop: no `hentry` hypothesis in context — run `py_begin [<prog>]` first
```

**`py_begin`/`py_loop` on a loop-free function:**

```
error: py_loop: no `execWhile` occurrence found in `hentry` — is there a loop?
```

Use `py_prove` — there is nothing for a loop rule to do.

**`dec` binders don't match `inv`:**

```
error: py_loop: `dec` must bind exactly the 2 variables of `inv`
```

**Wrong value in a straight-line spec** — the good failure: `py_prove` on
`square(x) ==> x + x` executes everything and leaves exactly the false
residue `⊢ x * x = x + x`. Fix the spec.

**Heartbeat timeout from `py_prove`** (`(deterministic) timeout at 'whnf',
maximum number of heartbeats (200000) has been reached`): symbolic execution
could not reduce to your claim. Two known causes: the program literal is
missing (`py_prove []` — pass `py_prove [tut_02]`), or an `==>!` spec names
the wrong exception ([tutorial 05](05-exceptions-and-partial.md#what-can-go-wrong)).

**Body outside the v1 loop recipe** (`return`/`break` in the body,
non-`Int` loop variable):

```
error: py_loop: could not derive the body's logical step (the `hbody` obligation did not close — body shape outside the v1 recipe)
```

A feature boundary — see the v1 restrictions in the
[`LoopTactic.lean` docstring](../../LeanModels/Python/LoopTactic.lean).

## Still stuck?

Reduce to a `#py_check`/`#eval` on concrete inputs first (is the *program*
doing what you think?), then to the manual script of
[tutorial 03 §4](03-branching-and-preconditions.md#4-reading-a-goal-state)
(where does the residue differ from your expectation?). The goal state is
the interface; the frozen atom in it — `execWhile`, an `ite`, a
`callFunction` — names the thing you still owe the proof.
