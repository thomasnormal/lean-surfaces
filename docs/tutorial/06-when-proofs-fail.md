# Tutorial 06 — When proofs fail

Every error below was reproduced against the current tree (scratch files
under `/tmp`, programs from `Examples/`), and every quoted message is
pasted, not paraphrased. Format: **symptom → diagnosis → fix**. Most fixed
versions live in [`Examples/python/tut_06/`](../../Examples/python/tut_06/tut_06.py)
(modes 5 and 7 point at their own examples):

```python
# Examples/python/tut_06/tut_06.py
def count_up(n):
    i = 0
    while i < n:
        i += 1
    return i


def true_div(a, b):
    return a / b
```

```lean
-- Examples/python/tut_06/proof.lean (header comment elided)
/-- Failure modes 1 and 2, fixed: `count_up` has a loop, so `py_prove`
cannot close it — `py_begin`/`py_loop` with the *right* invariant can.
The invariant needs both the range conjuncts: dropping `i ≤ n` strands
the exit goal (tutorial 06 shows the stuck state). -/
theorem count_up_total (n : PyInt) (hn : 0 ≤ n) : tut_06.count_up(n) ==> n := by
  py_begin [tut_06]
  py_loop (inv := fun (i : Int) => 0 ≤ i ∧ i ≤ n)
          (dec := fun (i : Int) => (n - i).toNat)
  all_goals grind
```

```lean
-- Examples/python/tut_06/spec.lean (excerpt)
#py_check tut_06.count_up(5) = 5
#py_check tut_06.count_up(0) = 0
...
/-! Failure mode 6: `a / b` is true division — a float, outside the v0
semantic tier. The interpreter refuses *loudly* (`Res.unsupported`,
never a wrong value); `unsupported` has no surface arrow on purpose, so
the check stays a raw `#guard … matches`. -/
#guard (callFunction tut_06 "true_div" #[.int 7, .int 2] 100 matches .unsupported _)
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
`Examples/python/tut_06/proof.lean` above.

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
[`sum_to.py`](../../Examples/python/sum_to/sum_to.py), lambda binders `(s k)`
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

**Diagnosis.** `PyInt` is *definitionally* `Int`, but `omega` ingests a
comparison only when its head type is literally `Int` or `Nat` — its atom
matching is syntactic and does not unfold the brand. A comparison headed at
`PyInt` (`@LE.le PyInt …`, as a hypothesis over a `PyInt` binder
elaborates) is skipped wholesale, **whether it is a hypothesis or the
goal** — hence "No usable constraints found". Which operand decides the
head type? The *leftmost* one with an intrinsic type
([tutorial 03 §3](03-branching-and-preconditions.md#3-preconditions-are-hypotheses--one-gotcha)),
and ascriptions on branded variables are looked through. Facts produced
*by the tactics* (split hypotheses, `hcont`, `hinv*`) are built at `Int`
and unaffected; inside an already-`Int`-headed comparison, brand-headed
*atoms* are also fine (`relu_total`'s arms close although `max x 0` was
elaborated at `PyInt`). `grind` is unaffected everywhere (it matches up to
reducible unfolding) — which is why the house style closes loop residuals
with `grind`, and why this bites mostly around `py_prove` and hand-written
`omega` bullets.

**Fix.** Three cases.

*A hypothesis you wrote* — restate it at `Int`, with a genuinely
`Int`-typed term as the **left** operand:

```lean
have hx' : (0 : Int) ≤ x := hx    -- for hx : 0 ≤ x
have hx' : (0 : Int) ≥ x := hx    -- for hx : x ≤ 0 — flip to keep Int on the left
```

Ascribing the branded variable does not work, on either side or both:
`(x : Int) ≤ 0`, `x ≤ (0 : Int)`, and `(x : Int) ≤ (0 : Int)` all re-land
at `PyInt` (reproduced — each still fails exactly as above, and the
restated hypothesis prints identically to the original: no visible
difference is the tell). Real instance: `relu_of_nonneg` in
[`Examples/python/tut_03/proof.lean`](../../Examples/python/tut_03/proof.lean); the
flipped direction is the `negpart_of_nonpos` shape of
[tutorial 03 §3](03-branching-and-preconditions.md#3-preconditions-are-hypotheses--one-gotcha).

*A `by_cases` you are about to run* — `by_cases h1 : x < 0` over a `PyInt`
binder produces a brand-headed `h1` with the same problem. Either put an
`Int` term on the left here too (`by_cases h1 : (0 : Int) > x`), or keep
`omega` out of it: pass `h1` to `py_simp` as a rewrite and close with
`grind` ([`Examples/python/ag_clamp01/proof.lean`](../../Examples/python/ag_clamp01/proof.lean), mode 7).

*The goal itself* — a brand-headed goal comparison (typical: spec-side
`max`/`min` over `Py*` binders in a pure-math lemma of your own) cannot be
restated, and no hypothesis surgery helps (reproduced):

```lean
-- (illustrative — broken)
example (x : PyInt) : max 0 (min 1 x) ≤ 1 := by omega
```

fails with the same "No usable constraints found", while the identical
statement over `x : Int` closes. Switch the closer: `grind` proves both.

## 6. The loud `.unsupported` — you left the semantic tier

**Symptom.** Any of: a `#py_check` fails and the `#eval` diagnosis of mode 4
shows

```
LeanModels.Python.Res.unsupported "unsupported expression 'BinOp:Div'"
```

or the runner says

```console
$ lake exe leanmodels-run Examples/python/tut_06/tut_06.json true_div 7 2
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
refusal (`#guard … matches .unsupported _`, as `Examples/python/tut_06/spec.lean`
does), and whitelist it in the harness with `"expect": "unsupported"`
([`harness/cases.json`](../../harness/cases.json) does exactly this for
`true_div`).

## 7. py_prove on two sequential ifs — the branch recipe runs out

**Symptom.** The body is loop-free and branching — `py_prove`'s home turf —
yet it leaves the un-split branch nest of mode 1, with no `execWhile`
anywhere in it. Reproduced against
[`ag_clamp01.py`](../../Examples/python/ag_clamp01/ag_clamp01.py):

```python
# Examples/python/ag_clamp01/ag_clamp01.py (function only)
def clamp01(x):
    if x < 0:
        return 0
    if x > 1:
        return 1
    return x
```

```lean
-- (illustrative — broken)
theorem clamp01_total (x : PyInt) : ag_clamp01.clamp01(x) ==> max 0 (min 1 x) := by
  py_prove [ag_clamp01]
```

```
error: unsolved goals
x : PyInt
⊢ ∃ a b,
    (∃ a_1 b_1,
        (∃ a,
            (if x < 0 then Res.ok (Val.bool true) else Res.ok (Val.bool false)) = Res.ok a ∧
...
```

**Diagnosis.** A known v0 limitation of `py_prove`. Its branch alternative
is a *single* `split <;> py_simp <;> omega` round, which handles one
symbolic branch point. With two *sequential* `if`s, the arm that falls
through to the second `if` gets re-executed by `py_simp`'s full simp set,
which rewrites the surviving `ite` into a disjunction that `split` can no
longer attack — run the manual script of
[tutorial 03 §4](03-branching-and-preconditions.md#4-reading-a-goal-state)
and the second `split` says so directly (reproduced):

```
error: Tactic `split` failed: Could not split an `if` or `match` expression in the goal
```

So read the `py_prove` docstring's "straight-line *and branching*" as "one
symbolic branch point"; nested/sequential branching needs the recipe below
(the GOAL-SHAPE table in [AGENTS.md](../../AGENTS.md) carries the same
caveat).

**Fix.** Decide the branch conditions *before* executing: `by_cases` each
condition up front, pass the case facts to `py_simp` as rewrites so every
`if` reduces during symbolic execution, and close with `grind` — not
`omega`: the `by_cases` hypotheses over the `PyInt` binder are
brand-headed (mode 5). The working proof, verbatim:

```lean
-- Examples/python/ag_clamp01/proof.lean (excerpt; statement re-stated in Examples/python/ag_clamp01/spec.lean)
theorem clamp01_total (x : PyInt) : ag_clamp01.clamp01(x) ==> max 0 (min 1 x) := by
  refine ⟨32, ?_⟩
  by_cases h1 : x < 0 <;> by_cases h2 : 1 < x <;>
    py_simp [callFunction, ag_clamp01, h1, h2] <;> grind
```

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
maximum number of heartbeats (200000) has been reached` — the location tag
after `timeout at` varies with elaborator state): symbolic execution
could not reduce to your claim. Two known causes: the program literal is
missing (`py_prove []` — pass `py_prove [tut_02]`), or an `==>!` spec names
the wrong exception ([tutorial 05](05-exceptions-and-partial.md#what-can-go-wrong)).

**Variable-headed simp warning on a raw `@[spec]` corollary:**

```
warning: Left-hand side of simp theorem has a variable as head symbol. This means the theorem will be tried on every simp step, which can be expensive. This may be acceptable for `local` or `scoped` simp lemmas.
Use `set_option warning.simp.varHead false` to disable this warning.
```

Not a mistake — the raw ∀-fuel form *is* a conditional simp lemma whose
rewrite head is the bound result variable, deliberately
([tutorial 04](04-loops.md#e-worked-end-to-end), notes). Prefix the
declaration with `set_option warning.simp.varHead false in`, as every
example file does.

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
