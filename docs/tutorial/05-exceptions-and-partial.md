# Tutorial 05 — Exceptions and partial correctness

Two more arrows complete your vocabulary: `==>!` ("terminates by raising")
and `~~>` (strengthened partial correctness). Along the way: why the weak
partial form is deliberately *not offered*, and the `gcd` sign bug — the
house cautionary tale about writing specs before differential testing.

## 1. The file

```python
# Examples/python/tut_05.py
def pymod(a, b):
    return a % b


def countdown(n):
    while n > 0:
        n -= 1
    return n


# lean[
# /-! Tutorial 05 (docs/tutorial/05-exceptions-and-partial.md): the `==>!`
# arrow for raising runs, the strengthened partial arrow `~~>`, and why
# the weak "if it returns then v" form is banned. -/
# #py_check tut_05.pymod(7, 3) = 1
# #py_check tut_05.pymod(-7, 3) = 2
# #py_check tut_05.pymod(7, -3) = -2
# #py_check tut_05.pymod(7, 0) raises .zeroDivisionError
# #py_check tut_05.countdown(5) = 0
# #py_check tut_05.countdown(0) = 0
# #py_check tut_05.countdown(-3) = -3
#
# /-- A raise as specified behavior: for every `a`, `pymod(a, 0)`
# terminates by raising `ZeroDivisionError`. `py_prove` closes `==>!`
# goals for loop-free bodies just like `==>` ones. -/
# theorem pymod_zero_raises (a : PyInt) : tut_05.pymod(a, 0) ==>! .zeroDivisionError := by
#   py_prove [tut_05]
#
# /-- Total correctness of the countdown for `n ≥ 0` — a single-clause
# loop proof. The theorem binder `n` shadows the mutated Python variable
# `n`, so `(state := [n])` names the environment slot and the lambda
# binder is free to be `k` (tutorial 04's shadowing trap). -/
# theorem countdown_total (n : PyInt) (hn : 0 ≤ n) : tut_05.countdown(n) ==> (0 : Int) := by
#   py_begin [tut_05]
#   py_loop (state := [n])
#           (inv := fun (k : Int) => 0 ≤ k)
#           (dec := fun (k : Int) => k.toNat)
#   all_goals grind
#
# /-- The strengthened partial arrow: every run of `countdown(n)` with
# `n ≥ 0`, at every fuel, either times out or returns exactly `0` — no
# exception, no `unsupported`, no other value. Free from `countdown_total`
# by determinism modulo fuel (`CallsTo.partialTo`, via `py_corollary`). -/
# theorem countdown_partial (n : PyInt) (hn : 0 ≤ n) : tut_05.countdown(n) ~~> (0 : Int) := by
#   py_corollary [countdown_total]
#
# /-- Why the weak reading is banned: `~~>` is *falsifiable* on raising
# programs. "If `pymod(7, 0)` returns, it returns 42" is vacuously true —
# the call raises. The strengthened `pymod(7, 0) ~~> 42` is refutable, and
# here is the refutation (`PartialTo.not_raises`, Surface.lean). -/
# theorem no_partial_spec_for_raising_call : ¬ (tut_05.pymod(7, 0) ~~> (42 : Int)) :=
#   fun h => h.not_raises (pymod_zero_raises 7)
# ]
```

## 2. `==>!` — a raise is a postcondition, not a failure

v0 Python has no `try`/`raise` statements, but *runtime* errors are real and
faithful: `%` by zero is a genuine `ZeroDivisionError`, and CPython agrees
(the `pymod(7, 0)` harness case matches). `pymod_zero_raises` makes the
raise the *specified behavior* — `==>!` elaborates to
`∃ fuel, callFunction … = .exn e` — and `py_prove` closes it the same way it
closes `==>` goals. Exceptions never need to be "excluded" from a spec; they
are one of the outcomes you state. (Gallery example 4 in
[../spec-surface.md](../spec-surface.md) scales this to `raise` proper;
recipe: [../howto/spec-a-raising-function.md](../howto/spec-a-raising-function.md).)

Note `.zeroDivisionError` is a `PyErr` constructor —
[../reference.md](../reference.md) tables the five v0 errors and their
CPython names.

## 3. `~~>` — partial correctness, the strengthened form

`countdown_partial` says: **every** run of `countdown(n)`, at **every**
fuel, either times out or returns exactly `0`. Unfolded
([`Surface.lean`](../../LeanModels/Python/Surface.lean), `PartialTo`):

```lean
-- (illustrative — the definition, verbatim from Surface.lean)
def PartialTo (m : Module) (f : String) (args : Array Val) (v : Val) : Prop :=
  ∀ fuel r, callFunction m f args fuel = r → r = .timeout ∨ r = .ok v
```

So a terminating outcome can be neither an exception, nor `unsupported`,
nor a different value. What it does *not* assert is termination — a
diverging call satisfies `~~> v` for every `v` (`PartialTo.of_diverges`),
which is exactly why no termination measure is needed to prove it.

And you rarely prove it directly: the interpreter is deterministic modulo
fuel, so **total correctness subsumes it** — `countdown_partial` is one
`py_corollary [countdown_total]`. You state `~~>` when termination is out of
reach or out of scope (the framework can state, e.g., the Collatz conjecture
— gallery example 8); you get it for free when you already have `==>`.

## 4. Why the weak form is banned

The textbook partial-correctness reading — "*if* the call returns a value,
it is `v`" — is not offered by this framework, deliberately. That form is
vacuously provable whenever the callee raises or diverges: `pymod(7, 0)`
raises, so "if `pymod(7, 0)` returns, it returns 42" is a theorem — for 42,
for 17, for anything. For an AI prover graded on proved specs, that is a
reward waiting to be hacked: the easiest route to "if it returns then `v`"
is making sure the premise never fires, and a prover *will* find that route.
The strengthened `~~>` closes it: `no_partial_spec_for_raising_call` above
is an actual refutation, in the tree, of the 42-spec — one line from
`PartialTo.not_raises`. Falsifiability is the design requirement; the bake-off
verdict and the `Obs`-spine machinery behind it are recorded in
[../spec-surface.md](../spec-surface.md) (judgment table and §10) and the
[`Surface.lean`](../../LeanModels/Python/Surface.lean) `PartialTo`/connectives
docstrings.

## 5. The cautionary tale: `gcd` and the sign of `%`

[`Examples/gcd/`](../../Examples/gcd/spec.lean) is the worked partial/total
pair in the tree (three-file layout: the program in `gcd.py`, statements and
checks in `spec.lean`, proofs in `proof.lean`) — read `spec.lean` now; it is
short. The theorem you would naively write is

```lean
-- (illustrative — this statement is FALSE, do not add it to a file)
theorem gcd_wrong (a b : PyInt) : gcd(a, b) ==> Int.gcd a b
```

It is false. Python's `%` is `Int.fmod` (sign follows the divisor), so
`gcd(4, -6)` iterates `4 % -6 = -2` and terminates at `-2`, while
`Int.gcd 4 (-6) = 2`. The file documents the divergence as executable
checks, verbatim:

```lean
-- Examples/gcd/spec.lean (excerpt)
#py_check gcd(4, -6) = -2
#guard Int.gcd 4 (-6) == 2
```

and the honest theorems carry sign hypotheses (`0 ≤ a`, `0 ≤ b`) — with the
loop proof shaped exactly like tutorial 04 taught you (note
`(state := [a, b])`: the loop mutates both, and the invariant
`Int.gcd x y = Int.gcd a b` must mention the initial values):

```lean
-- Examples/gcd/proof.lean (excerpt; statements re-stated in Examples/gcd/spec.lean)
theorem gcd_total (a b : PyInt) (ha : 0 ≤ a) (hb : 0 ≤ b) : gcd(a, b) ==> Int.gcd a b := by
  py_begin [gcd]
  py_loop (state := [a, b])
          (inv := fun (x y : Int) => 0 ≤ x ∧ 0 ≤ y ∧ Int.gcd x y = Int.gcd a b)
          (dec := fun (x y : Int) => y.toNat)
  · grind [Int.gcd_zero_right, Int.natAbs_of_nonneg]
  · exact ⟨hinv2, Int.fmod_nonneg hinv1 hinv2, by rw [gcd_fmod_step hinv1 hinv2, hinv3]⟩
  · have := Int.fmod_lt_of_pos x (show (0:Int) < y by omega)
    have := Int.fmod_nonneg hinv1 hinv2
    omega
  · exact ⟨ha, hb, trivial⟩

theorem gcd_partial (a b : PyInt) (ha : 0 ≤ a) (hb : 0 ≤ b) : gcd(a, b) ~~> Int.gcd a b := by
  py_corollary [gcd_total]
```

The bug was caught by **differentially testing the executable model against
CPython before proving anything** — `gcd(4, -6)` sits in
[`harness/cases.json`](../../harness/cases.json) to this day. Had the weak
partial form existed, the false unguarded spec would have been *provable*
on the raising/diverging fringe instead of caught. Hence the methodology,
mandatory and in this order: **spec → `#py_check`/diff-test → prove**
([../spec-surface.md](../spec-surface.md) §3, §10).

Next: [tutorial 06](06-when-proofs-fail.md) — everything that goes wrong,
with the real error for each.

## What can go wrong

**Wrong exception in an `==>!` spec.** State `.valueError "nope"` where the
program raises `ZeroDivisionError` and `py_prove` does not fail cleanly — it
times out (reproduced):

```
error: Tactic `simp` failed with a nested error:
(deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached
```

A heartbeat timeout from `py_prove` means symbolic execution could not
reach your claimed result — check the spec (and see
[tutorial 06, bonus modes](06-when-proofs-fail.md#bonus-quick-hits)).

**Expecting `~~>` to prove termination.** It cannot, ever
(`PartialTo.of_diverges`). If you need termination, prove `==>` — possibly
with extra hypotheses — and downgrade with `py_corollary`; or wait for
`Py.Terminates` (designed, not yet built —
[../spec-surface.md](../spec-surface.md)).

**Stating `~~>` without the guarding hypotheses.** `countdown(-3)` returns
`-3` (check the `#py_check` line), so `countdown(n) ~~> 0` without
`0 ≤ n` is simply false — a decided run returning `-3` contradicts it. The
arrows are falsifiable by design; when a `~~>` proof will not close, run the
function on the fringe inputs first.
