# How to spec a raising function

A raise is a first-class postcondition, not an error to exclude: the `==>!`
arrow states "terminates by raising this error". Elaboration:
[reference](../reference.md#the-judgment-family); error classes:
[reference](../reference.md#error-classes).

## What "raising" means in v0

The v0 tier has **no `raise` statement** — the extractor emits `raise` as an
`Unsupported` node and the interpreter refuses it loudly. What v0 *does*
have, faithfully, are runtime errors: `TypeError`, `NameError`,
`ZeroDivisionError`, `IndexError`, `ValueError` (from tuple-unpack arity).
So a v0 raising spec is about an error the code *runs into* — a zero
divisor, an out-of-range index — not one it constructs.

## State the check, then the theorem

Non-vacuity first, in surface syntax (real file, checked by `lake build`):

```lean
-- Examples/python/arith/spec.lean (two lines from the check block)
#py_check arith.floordiv(7, 0) raises .zeroDivisionError
#py_check arith.idx(3) raises .indexError
```

Then the universally quantified theorem — stated in `spec.lean`:

```lean
-- Examples/python/arith/spec.lean (excerpt)
/-- Exceptions as specified behavior (docs/spec-surface.md example 4, in
its v0 form: the tier has no `raise` statement, but *runtime* errors are
real and provable): `floordiv(a, 0)` terminates by raising
`ZeroDivisionError`, for every `a` — the `==>!` arrow (`Raises`,
Surface.lean). The error path is loop-free, so `py_prove` closes it
(`Examples/python/arith/proof.lean`). -/
theorem floordiv_zero (a : PyInt) : arith.floordiv(a, 0) ==>! .zeroDivisionError := by proofs

/-- Same shape for `%`: `mod(a, 0)` raises for every `a`. -/
theorem mod_zero (a : PyInt) : arith.mod(a, 0) ==>! .zeroDivisionError := by proofs
```

The error path of `floordiv` (`return a // b` with `b = 0`) is loop-free,
so `py_prove` closes it in the proof module:

```lean
-- Examples/python/arith/proof.lean (excerpt; docstrings elided)
theorem floordiv_zero (a : PyInt) : arith.floordiv(a, 0) ==>! .zeroDivisionError := by
  py_prove [arith]

theorem mod_zero (a : PyInt) : arith.mod(a, 0) ==>! .zeroDivisionError := by
  py_prove [arith]
```

`==>!` elaborates to `Raises`: some fuel makes `callFunction` return exactly
`.exn e`. By determinism (`CallsTo.not_raises`, `PartialTo.not_raises`), a
proved `==>!` is mutually exclusive with any `==>` or `~~>` on the same call
— the naive "if it returns a value, then …" spec would be vacuously true on
this input; `==>!` is the falsifiable statement of what actually happens.

If the error sits behind a loop or in only one branch, the value-vs-error
split is a pair of guarded theorems (one `==>`, one `==>!`) with disjoint
hypotheses — see the `first_index` gallery entry in
[spec-surface.md §4](../spec-surface.md) for the intended shape (its `raise`
needs a later tier, but the two-theorem pattern applies to v0 runtime errors
as-is).

## What can go wrong

**Message-carrying errors are exact-match.** `==>!` compares the whole
`PyErr` value. `.zeroDivisionError` and `.indexError` carry no payload and
are the practical targets. `.typeError`/`.valueError`/`.nameError` carry a
message/name string, and your spec must match it character-for-character
(the interpreter's messages mimic CPython's, e.g.
`.typeError "unsupported operand type(s) for +: 'int' and 'str'"`).

**Heartbeat timeout on string-valued calls.** (Verified on the current
tree.) A `==>!` goal whose call carries a *string argument* — e.g.
`add(a, "x") ==>! .typeError "…"` — sends `py_prove`'s symbolic execution
into a heartbeat timeout: `` (deterministic) timeout at `whnf`, maximum
number of heartbeats (200000) has been reached `` (the reported site varies
— the wrong-error case below dies at `isDefEq`). Symbolic string equality
blows up in reduction/defeq checking. Practical v0 raising specs stay on
int inputs; pin string-input error behavior with `#py_check … raises …`
(concrete evaluation, cheap) instead of a theorem.

**Wrong error value.** (Verified.) A wrong error class under `py_prove` —
e.g. claiming `arith.mod(a, 0) ==>! .indexError` — does *not* fail with a
readable mismatch: `py_prove`'s fallback alternatives churn until a
`` (deterministic) timeout at `isDefEq` `` heartbeat error. A heartbeat timeout
on a raising spec therefore usually means "wrong claim", not "hard proof".
Check what really happens first:

```
lake exe leanmodels-run Examples/python/arith/arith.json mod 7 0
{"status":"exn","exn":"ZeroDivisionError"}
```

**Expecting `raise` to work.** A function whose body contains `raise` calls
into an `Unsupported` statement node; the interpreter answers
`Res.unsupported`, which no `==>!` can match (and no `#py_check` form
states — use a raw `#guard … matches .unsupported _` if you need to pin
that). See
[check-what-the-extractor-supports.md](check-what-the-extractor-supports.md).

**`UnboundLocalError` in the harness.** CPython raises the subclass; the
model and harness canonicalize to `NameError`
([reference](../reference.md#error-classes)) — differential rows on such
functions still match.
