/-
Examples/python/bench_statistics — three-file example layout (see
Examples/python/tri/spec.lean for the pattern rationale):
bench_statistics.py (vendored BYTE-VERBATIM from CPython 3.9.25
statistics.py — provenance and per-segment sha256 in its module
docstring), bench_statistics.json (generated envelope), THIS FILE
(statements, `:= by proofs`), proof.lean (the real proofs, namespace
`Examples.python.bench_statistics.proof`).

BENCHMARK FLAGSHIP (Band C, docs/benchmark.md rows 4-5): CPython's own
`median_low`/`median_high`, proved totally correct against their ACTUAL
shipped source through the builtin `sorted` — the call:sorted tier
feature. `median` (row 3) stays honestly blocked: its even-length branch
is float division (`(a+b)/2`), out of `Val` v0.

Tier facts (envelope, unchanged since vendoring — call:sorted needed NO
extractor or envelope change, `sorted(data)` was always a plain in-tier
`Call` node):
* Both functions: `args_unsupported: null`; `data = sorted(data)` is
  `Call` with `func: Name "sorted"`, one positional arg,
  `call_unsupported: null`; the SOLE `Unsupported` node per function is
  the `raise StatisticsError` guard behind `if n == 0` — unreachable for
  `data ≠ []`, so the theorems below cover the byte-verbatim body with
  its exception path intact (rsa_inverse/bisect precedent). The
  `#guard … matches .unsupported` lines document the edge: an empty list
  DOES reach the raise and the interpreter refuses loudly.
* `sorted` semantics (v0, DESIGN.md): all-int list → NEW ascending list
  (`sortInts`, a kernel-reducible insertion sort); wrong arity /
  non-iterable → honest `TypeError`; str/tuple/non-int elements →
  loud `unsupported` (CPython succeeds there — v0 does not guess);
  `key=`/`reverse=` are keyword-only, refused as
  `call_unsupported: "keywords"`.
* Both bodies are STRAIGHT-LINE (no loops) — the cores are single
  `py_simp` symbolic executions (no loop lemmas needed).

Non-vacuity gap (recorded per AGENTS.md): `harness/cases.json` rows with
LIST arguments are inexpressible — `leanmodels-run` parses CLI args as
ints only (bisect precedent) — so the CPython-3.9.25 ground-truth table
(docs/benchmark.md, medians probe table; checked against the vendored
file via importlib exactly as diff_test.py does) is pinned as the
`#py_check` rows below. The int-arg edges (not-iterable, arity) ARE in
cases.json as `"match"` rows.
-/
import Examples.python.bench_statistics.proof

open LeanModels LeanModels.Python

load_program bench_statistics from "Examples/python/bench_statistics/bench_statistics.json"

/-! Non-vacuity: the CPython 3.9.25 ground-truth table in surface syntax
(`#py_check`, fixed generous fuel). Odd/even lengths, unsorted inputs,
duplicates, negatives, singleton, two-element, all-equal. -/
#py_check bench_statistics.median_low([1, 3, 5]) = 3
#py_check bench_statistics.median_high([1, 3, 5]) = 3
#py_check bench_statistics.median_low([5, 1, 3]) = 3
#py_check bench_statistics.median_high([5, 1, 3]) = 3
#py_check bench_statistics.median_low([1, 3, 5, 7]) = 3
#py_check bench_statistics.median_high([1, 3, 5, 7]) = 5
#py_check bench_statistics.median_low([7, 1, 5, 3]) = 3
#py_check bench_statistics.median_high([7, 1, 5, 3]) = 5
#py_check bench_statistics.median_low([2, 2, 1, 3]) = 2
#py_check bench_statistics.median_high([2, 2, 1, 3]) = 2
#py_check bench_statistics.median_low([4, 1, 4]) = 4
#py_check bench_statistics.median_high([4, 1, 4]) = 4
#py_check bench_statistics.median_low([-5, 3, -1, 0]) = -1
#py_check bench_statistics.median_high([-5, 3, -1, 0]) = 0
#py_check bench_statistics.median_low([-2, -7, -1]) = -2
#py_check bench_statistics.median_high([-2, -7, -1]) = -2
#py_check bench_statistics.median_low([42]) = 42
#py_check bench_statistics.median_high([42]) = 42
#py_check bench_statistics.median_low([2, 1]) = 1
#py_check bench_statistics.median_high([2, 1]) = 2
#py_check bench_statistics.median_low([-3, 9]) = -3
#py_check bench_statistics.median_high([-3, 9]) = 9
#py_check bench_statistics.median_low([0, 0, 0, 0]) = 0
#py_check bench_statistics.median_high([0, 0, 0, 0]) = 0

/-! Honest exception paths: a non-iterable argument TypeErrors inside
`sorted`, wrong arity TypeErrors at the call. The arity TEXT was a WRONG
FACT until 2026-08-16 — it read `median_low() takes 1 positional
arguments but 0 were given`, which is not a sentence CPython produces
(too FEW arguments is the MISSING form, and even the plural was wrong).
Measured live on 3.9.19. -/
#py_check bench_statistics.median_low(3) raises
  .typeError "'int' object is not iterable"
#py_check bench_statistics.median_high(7) raises
  .typeError "'int' object is not iterable"
#py_check bench_statistics.median_low() raises
  .typeError "median_low() missing 1 required positional argument: 'data'"

/-! Tier-edge documentation: the EMPTY list reaches the vendored
`raise StatisticsError('no median for empty data')` — the single
Unsupported node per function — and the interpreter refuses loudly
(`.unsupported`, never a fake Python result; on the vendored file CPython
itself raises `NameError: StatisticsError` since the exception class is
deliberately not vendored). The theorems below never touch it: `data ≠ []`
makes the guard concretely false. -/
#guard (callFunction bench_statistics "median_low" #[.list #[]] 4096
    matches .unsupported _)
#guard (callFunction bench_statistics "median_high" #[.list #[]] 4096
    matches .unsupported _)

/-! ## The theorems (statements duplicated from proof.lean BY DESIGN —
`:= by proofs` typechecks the duplication) -/

/-- **Main theorem (`median_low`).** For every nonempty int list, CPython's
`median_low` — run byte-verbatim through the deep-embedded interpreter —
terminates and returns the element at sorted rank `⌊(n−1)/2⌋` (odd `n`:
the middle; even `n`: the lower middle — one rank expression covers both
vendored branches). -/
theorem median_low_total (data : List PyInt) (hne : data ≠ []) :
    bench_statistics.median_low(data) ==>
      (sortInts data).getD ((data.length - 1) / 2) 0 := by proofs

/-- **Main theorem (`median_high`).** The element at sorted rank `⌊n/2⌋`. -/
theorem median_high_total (data : List PyInt) (hne : data ≠ []) :
    bench_statistics.median_high(data) ==>
      (sortInts data).getD (data.length / 2) 0 := by proofs

/-- **Rank characterization (`median_low`, `⇓`-relational)**: any observed
result is an element of the data, with at least `⌊(n−1)/2⌋ + 1` data
elements `≤` it and at least `n − ⌊(n−1)/2⌋` data elements `≥` it — the
order-statistics contract over SYMBOLIC data, not "index into sorted()". -/
theorem median_low_rank (data : List PyInt) (hne : data ≠ []) {r : PyInt}
    (h : bench_statistics.median_low(data) ⇓ r) :
    r ∈ data ∧
      (data.length - 1) / 2 + 1 ≤ data.countP (fun v => decide (v ≤ r)) ∧
      data.length - (data.length - 1) / 2
        ≤ data.countP (fun v => decide (r ≤ v)) := by proofs

/-- **Rank characterization (`median_high`, `⇓`-relational)**. -/
theorem median_high_rank (data : List PyInt) (hne : data ≠ []) {r : PyInt}
    (h : bench_statistics.median_high(data) ⇓ r) :
    r ∈ data ∧
      data.length / 2 + 1 ≤ data.countP (fun v => decide (v ≤ r)) ∧
      data.length - data.length / 2
        ≤ data.countP (fun v => decide (r ≤ v)) := by proofs

/-- **Strengthened partial correctness (`median_low`, `~~>`)**: every run,
at every fuel, either times out or returns exactly the low median — no
exception, no `unsupported`, no other value. -/
theorem median_low_partial (data : List PyInt) (hne : data ≠ []) :
    bench_statistics.median_low(data) ~~>
      (sortInts data).getD ((data.length - 1) / 2) 0 := by proofs

/-- **Strengthened partial correctness (`median_high`, `~~>`)**. -/
theorem median_high_partial (data : List PyInt) (hne : data ≠ []) :
    bench_statistics.median_high(data) ~~>
      (sortInts data).getD (data.length / 2) 0 := by proofs

/-- **Low ≤ high**: on the same data, any observed `median_low` result is
`≤` any observed `median_high` result. -/
theorem median_low_le_median_high (data : List PyInt) (hne : data ≠ [])
    {lo hi : PyInt} (hlo : bench_statistics.median_low(data) ⇓ lo)
    (hhi : bench_statistics.median_high(data) ⇓ hi) :
    lo ≤ hi := by proofs

/-- **Pre-sorted input (`median_low`)**: on already-ascending data the low
median is literally `data[(n−1)/2]` (`sortInts` fixpoint). -/
theorem median_low_presorted (data : List PyInt) (hne : data ≠ [])
    (hs : data.Pairwise (· ≤ ·)) :
    bench_statistics.median_low(data) ==>
      data.getD ((data.length - 1) / 2) 0 := by proofs

/-- **Pre-sorted input (`median_high`)**: `data[n/2]`. -/
theorem median_high_presorted (data : List PyInt) (hne : data ≠ [])
    (hs : data.Pairwise (· ≤ ·)) :
    bench_statistics.median_high(data) ==>
      data.getD (data.length / 2) 0 := by proofs

/-! ## Axiom audit (house bar, AGENTS.md): each line must print exactly
`[propext, Classical.choice, Quot.sound]`. The explicit in-tree block is
adopted from the cold-prover deliverables (docs/benchmark.md,
"Cold-prover runs (2026-07-31 — the medians)"). -/
#print axioms median_low_total
#print axioms median_high_total
#print axioms median_low_rank
#print axioms median_high_rank
#print axioms median_low_partial
#print axioms median_high_partial
#print axioms median_low_le_median_high
#print axioms median_low_presorted
#print axioms median_high_presorted
