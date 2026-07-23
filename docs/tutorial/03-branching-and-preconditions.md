# Tutorial 03 — Branching and preconditions

Straight-line code is done. This part adds `if`, preconditions as ordinary
hypotheses, and — because you will spend your life looking at them — how to
read a goal state when `py_prove` is *not* doing everything for you, plus
what the delaborators show you versus what is really there.

## 1. The files

`Examples/python/tut_03/`, three-file layout as before. The program:

```python
# Examples/python/tut_03/tut_03.py
def relu(x: int) -> int:
    if x < 0:
        return 0
    return x
```

The statements live in
[`Examples/python/tut_03/spec.lean`](../../Examples/python/tut_03/spec.lean) (each
`:= by proofs`, plus a `#guard_msgs`/`#check` delaborator regression that
§5 explains); this tutorial is about the *proofs*, so here is the proof
module in full:

```lean
-- Examples/python/tut_03/proof.lean (header comment elided)
import LeanModels

namespace Examples.python.tut_03.proof

open LeanModels LeanModels.Python

load_program tut_03 from "Examples/python/tut_03/tut_03.json"

/-- Unconditional total correctness: `py_prove` splits the symbolic
branch left by `if x < 0:` and closes both arms with `omega` (which
knows `max`). -/
theorem relu_total (x : PyInt) : tut_03.relu(x) ==> max x 0 := by
  py_prove [tut_03]

/-- With a precondition: the `have` line re-lands `hx` at `Int` for
`py_prove`'s `omega` closer (docs/tutorial/06-when-proofs-fail.md,
failure mode 5). -/
theorem relu_of_nonneg (x : PyInt) (hx : 0 ≤ x) : tut_03.relu(x) ==> x := by
  have hx' : (0 : Int) ≤ x := hx
  py_prove [tut_03]

/-- The same theorem with the proof spelled out, for reading goal states
(docs/tutorial/03-branching-and-preconditions.md walks through each
step's goal). -/
theorem relu_of_nonneg' (x : PyInt) (hx : 0 ≤ x) : tut_03.relu(x) ==> x := by
  have hx' : (0 : Int) ≤ x := hx
  refine ⟨32, ?_⟩
  py_simp [callFunction, tut_03]
  split <;> py_simp
  omega

end Examples.python.tut_03.proof
```

## 2. Branching: the `my_abs` pattern

`relu_total` is the [`my_abs`](../../Examples/python/my_abs/my_abs.py) pattern from
the gallery ([../spec-surface.md](../spec-surface.md) §1): the Python branch
condition `x < 0` is symbolic — the interpreter cannot decide it for an
arbitrary `x` — so symbolic execution leaves an `ite` in the goal. `py_prove`
handles this itself: its branch-splitting alternative runs `split`,
re-executes each arm, and finishes with `omega`. One tactic call still
suffices; the spec-side `max x 0` is understood natively by `omega`.

One branch *point*, that is. A second sequential `if` in the same body is
outside `py_prove`'s single-round recipe — a known v0 limitation, with a
loud symptom and a short `by_cases` recipe that replaces it:
[tutorial 06, mode 7](06-when-proofs-fail.md#7-py_prove-on-two-sequential-ifs--the-branch-recipe-runs-out).

## 3. Preconditions are hypotheses — one gotcha

A precondition is nothing special: an ordinary named hypothesis, exactly as
in any Lean theorem. `relu_of_nonneg` says `relu` is the identity *given*
`0 ≤ x`, and the branch `x < 0` is discharged by contradiction with it.

The gotcha is the `have hx' : (0 : Int) ≤ x := hx` line. Binder brands
(`PyInt`) are definitionally `Int`, but a hypothesis *stated over* them —
`hx : 0 ≤ x` with `x : PyInt` — carries `PyInt`-headed instances, and
`omega`'s syntactic atom matching does not see through them. `py_prove` ends
in `omega`, so without the restatement the contradiction is invisible and
the proof fails ([tutorial 06, failure mode
5](06-when-proofs-fail.md#5-omega-ignores-a-pyint-typed-hypothesis) has the
raw error). `grind` is not affected, and the loop tactics of
[tutorial 04](04-loops.md) mostly shield you; for `py_prove`, restate the
hypothesis at `Int` (one `have`) and move on.

One more thing to know before you write that `have`: it is
**position-sensitive**. What lands `hx'` at `Int` is not the ascription as
such — it is the genuinely `Int`-typed term (here the literal `(0 : Int)`)
standing as the *left* operand: the comparison elaborator resolves the
relation's type from its leftmost intrinsically-typed operand, and it looks
straight through ascriptions on branded variables. Write the precondition
the other way around (`hx : x ≤ 0`) and the natural transcriptions
`(x : Int) ≤ 0`, `x ≤ (0 : Int)` — even `(x : Int) ≤ (0 : Int)` — all
re-land at `PyInt`; the restatement that works flips the relation to put
the literal first. The mirror-image shape (a `neg_part` returning `-x` on
nonpositive inputs):

```lean
-- (illustrative — the flipped-precondition restatement; reproduced against a scratch program)
theorem negpart_of_nonpos (x : PyInt) (hx : x ≤ 0) : neg_part(x) ==> -x := by
  have hx' : (0 : Int) ≥ x := hx
  py_prove [neg_part]
```

The reproduced failures, and the goal-side variant of the same blindness
that no restatement can fix, are in [tutorial 06, mode
5](06-when-proofs-fail.md#5-omega-ignores-a-pyint-typed-hypothesis).

## 4. Reading a goal state

`relu_of_nonneg'` proves the same theorem with the automation unrolled.
Follow along in your editor (open `Examples/python/tut_03/proof.lean`) — the
states below are captured verbatim from the current tree.

**Step 0 — the goal as stated.** Before any tactic:

```
⊢ tut_03.relu(x) ==> x
```

That *display* is the delaborator at work (§5). The proposition underneath
is `CallsTo tut_03 "relu" #[ToVal.toVal x] (ToVal.toVal x)`, i.e.
`∃ fuel, callFunction … = .ok …`.

**Step 1 — `refine ⟨32, ?_⟩`.** Commit a fuel witness (any generous constant;
32 covers every loop-free body). You have stepped *below the judgment
boundary*, and nothing is sugared any more:

```
x : PyInt
hx : 0 ≤ x
hx' : 0 ≤ x
⊢ callFunction tut_03 "relu" #[ToVal.toVal x] 32 = Res.ok (ToVal.toVal x)
```

**Step 2 — `py_simp [callFunction, tut_03]`.** Symbolically execute:
`py_simp` is `simp` with the interpreter's equations
([`Logic.lean`](../../LeanModels/Python/Logic.lean)); passing `tut_03`
unfolds the program literal, and passing `callFunction` is safe here because
there is no recursion to protect. The result is the interpreter's actual
control flow, reified — statement list, environment, `Flow` plumbing (elided
middle):

```
⊢ ∃ a b,
    (∃ a_1 b_1,
        (∃ a,
            (if x < 0 then Res.ok (Val.bool true) else Res.ok (Val.bool false)) = Res.ok a ∧
              (if
                    (match a with
                      | Val.none => false
                      | Val.bool b => b
                      ...
```

Don't panic; learn to skim it. The skeleton is a nest of `∃ env, flow`
pairs — one per executed statement — whose *atoms* are the parts the
interpreter could not decide. Here exactly one thing is symbolic: the
comparison `if x < 0 then … else …`. Everything else is concrete: you can
read the environment `[("x", Val.int x)]`, the two possible flows
(`Flow.ret (Val.int 0)` for the true arm, `Flow.next` falling through to
`return x`), and at the very bottom the target `Res.ok (Val.int x)`.

**Step 3 — `split <;> py_simp`.** Case-split the `ite`, then re-execute each
arm. The false arm (`¬ x < 0`: the function returns `x`, which is the spec)
closes outright; the true arm survives as pure arithmetic:

```
case isTrue
x : PyInt
hx : 0 ≤ x
hx' : 0 ≤ x
h✝ : x < 0
⊢ 0 = x
```

**Step 4 — `omega`.** `h✝ : x < 0` and `hx' : (0:Int) ≤ x` are
contradictory. Done. (`hx` alone would not have worked — §3.)

The pattern generalizes: **fuel witness → symbolic execution → case-split
the symbolic residue → arithmetic.** `py_prove` is precisely this script
with fallbacks; when it fails, run the script by hand and look at where the
residue is not what you expected.

## 5. What you see vs. what it is

The goal state is the interface — for a human and, just as deliberately, for
an AI prover. Three rules of thumb, all on display in this file:

- **At the judgment level you see arrows.** `#check relu_total` prints
  `relu_total (x : PyInt) : tut_03.relu(x) ==> max x 0` — the `#guard_msgs`
  block in the file pins this rendering as a regression test. Marshalling
  (`ToVal.toVal`) is stripped *inside judgment positions only*.
- **Below the boundary you see the machine.** After `refine ⟨32, ?_⟩` or
  `obtain ⟨fuel, h⟩ := relu_total x`, fuel and `callFunction` are visible —
  by design; you chose to step down.
- **`⇓` prints as `==>`.** Both are the same `CallsTo`; the unexpander
  cannot know which you wrote.

The complete contract — what unexpands, what deliberately still leaks
(`pp.explicit`, raw `Val` arguments, the `Obs` spine) — is in the
[`Delab.lean` module docstring](../../LeanModels/Python/Delab.lean). Read it
once; it is short and it is the authority.

Next: [tutorial 04](04-loops.md) — loops, the real thing.

## What can go wrong

**`py_prove` fails with a precondition present.** Symptom (reproduced;
elided middle):

```
error: unsolved goals
x : PyInt
hx : 0 ≤ x
⊢ ∃ a b,
    (∃ a_1 b_1,
        (∃ a,
            (if x < 0 then Res.ok (Val.bool true) else Res.ok (Val.bool false)) = Res.ok a ∧
...
```

`py_prove`'s branch alternative ran `split <;> py_simp <;> omega`, `omega`
could not see the `PyInt`-branded `hx`, the alternative failed, and the
fallback left the un-split goal. Fix: `have hx' : (0 : Int) ≤ x := hx`
first. Details: [tutorial 06, failure mode
5](06-when-proofs-fail.md#5-omega-ignores-a-pyint-typed-hypothesis).

**The restatement itself is still invisible.** With the precondition
running the other way (`hx : x ≤ 0`, the `neg_part` shape of §3),
restating by
ascription — `have hx' : x ≤ (0 : Int) := hx`, or `(x : Int) ≤ 0` —
changes nothing: `py_prove` fails with the same un-split dump, whose
context shows the tell (reproduced; elided below the turnstile):

```
error: unsolved goals
x : PyInt
hx : x ≤ 0
hx' : x ≤ 0
⊢ ∃ a b,
...
```

`hx'` prints exactly like `hx` — the ascription bought nothing (§3: the
relation's type comes from the leftmost intrinsically-typed operand). Put
the `Int` literal on the left: `have hx' : (0 : Int) ≥ x := hx`.

**`omega` right after `split`.** In the manual script, the arms are *not*
arithmetic yet — they are interpreter states (the arm still ends in
`Res.ok … = Res.ok …`). `split <;> omega` here closes the `x < 0` arm (its
hypotheses contradict `hx'`) but on the surviving arm reports, confusingly
(reproduced):

```
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  a ≥ 0
where
 a := x
```

— it saw the split hypothesis `¬x < 0` but no arithmetic *goal*. Re-execute
first: `split <;> py_simp`, then `omega`.

**Reading `⇓` output as a different judgment.** `#check square_result`
(tutorial 02) shows `==>` where the source said `⇓`. Same proposition,
display collapses them — do not hunt for a semantic difference.
