/-
Examples/python/bench_calendar — three-file example layout (see
Examples/python/tri/spec.lean for the pattern rationale): bench_calendar.py
(vendored BYTE-VERBATIM from CPython 3.9.25 calendar.py — provenance in
its module docstring), bench_calendar.json (generated envelope), THIS
FILE (statements, `:= by proofs`), proof.lean (the real proofs, namespace
`Examples.python.bench_calendar.proof`).

BENCHMARK TARGET (Band B, docs/benchmark.md rows 3-4): CPython's
`calendar.isleap` / `calendar.leapdays` — the first real-stdlib functions
the benchmark classified provable-now with ZERO blockers, proved against
their ACTUAL shipped source.

Tier facts (envelope): both functions fully in-tier, zero Unsupported
nodes, `args_unsupported: null`. `isleap` is one boolean-arithmetic
return; `leapdays` is two `AugAssign Sub`s and a FloorDiv/Sub/Add return.

PROVENANCE OF THE PROOFS: benchmark cold-prover run, 2026-07-30
(docs/benchmark.md "Cold-prover runs") — a fresh agent, repo docs only;
adapted here with statements unchanged. `leapdays_count` goes beyond the
row-4 candidate spec: not just the closed form, but the closed form =
an explicit per-year reference COUNT (`leapCount`, proof.lean), i.e.
"leapdays counts actual leap years", the function's own docstring.

Differential rows: harness/cases.json (isleap 12 rows, leapdays 10 rows,
incl. negative years and empty ranges) — all match CPython 3.9.25.

No `@[spec]` forms: `isleap` returns a `decide`-Bool and `leapdays` a
`leapCount` value — statement shapes kept exactly as proved; raw ∀-fuel
corollaries can be minted with `py_corollary` when a consumer needs them.
-/
import Examples.python.bench_calendar.proof

open LeanModels LeanModels.Python
open Examples.python.bench_calendar.proof (leapCount)

load_program bench_calendar from "Examples/python/bench_calendar/bench_calendar.json"

/-! Non-vacuity: concrete runs in surface syntax (`#py_check`,
Surface.lean — fixed generous fuel), matching the authenticity block of
bench_calendar.py (CPython 3.9.25, vendored file AND installed module). -/
#py_check bench_calendar.isleap(2024) = true
#py_check bench_calendar.isleap(1900) = false
#py_check bench_calendar.isleap(2000) = true
#py_check bench_calendar.isleap(2023) = false
#py_check bench_calendar.leapdays(1900, 2000) = 24
#py_check bench_calendar.leapdays(2000, 2026) = 7

/-! Non-vacuity of the reference count itself, against the same concrete
years (kernel `decide` via `#guard`, no `native_decide`): `leapCount 1899
100` counts leap years in `(1899, 1999] = [1900, 2000)`, matching
`leapdays(1900, 2000) = 24`; `leapCount 1999 26` matches
`leapdays(2000, 2026) = 7`. -/
#guard leapCount 1899 100 == 24
#guard leapCount 1999 26 == 7

/-- `isleap` decides the Gregorian leap-year rule exactly. -/
theorem isleap_spec (y : PyInt) :
    bench_calendar.isleap(y) ==> decide (Int.fmod y 4 = 0 ∧ (Int.fmod y 100 ≠ 0 ∨ Int.fmod y 400 = 0)) := by proofs

/-- `leapdays` computes exactly the CPython closed-form inclusion-exclusion
count (straight-line body: two `AugAssign`s then the arithmetic `return`). -/
theorem leapdays_arith (y1 y2 : PyInt) :
    bench_calendar.leapdays(y1, y2) ==>
      (((y2 - 1).fdiv 4 - (y1 - 1).fdiv 4)
        - ((y2 - 1).fdiv 100 - (y1 - 1).fdiv 100)
        + ((y2 - 1).fdiv 400 - (y1 - 1).fdiv 400)) := by proofs

/-- **The meaningful theorem.** For `y1 ≤ y2`, CPython's `leapdays(y1, y2)`
terminates and returns exactly the number of Gregorian leap years in the
half-open interval `[y1, y2)` — the `leapCount` reference count over
`(y1 - 1, y1 - 1 + (y2 - y1)] = (y1 - 1, y2 - 1] = [y1, y2)`, using the same
leap-year predicate `isleap_spec` proves the sibling function `isleap`
decides. -/
theorem leapdays_count (y1 y2 : PyInt) (h : y1 ≤ y2) :
    bench_calendar.leapdays(y1, y2) ==> leapCount (y1 - 1) (y2 - y1).toNat := by proofs
