/-
Examples/python/bench_bisect — three-file example layout (see
Examples/python/tri/spec.lean for the pattern rationale): bench_bisect.py
(vendored BYTE-VERBATIM from CPython 3.9.25 bisect.py — provenance in its
module docstring), bench_bisect.json (generated envelope), THIS FILE
(statements, `:= by proofs`), proof.lean (the real proofs, namespace
`Examples.python.bench_bisect.proof`).

BENCHMARK FLAGSHIP (Band A, docs/benchmark.md rows 1-2): CPython's own
`bisect_left`/`bisect_right` — the pure-Python reference implementations
the C accelerator replaces — proved totally correct against their ACTUAL
shipped source, with both parameter defaults engaged (`lo=0`,
`hi=None` → `hi = len(a)`, the F1/F2 tier features).

Tier facts (envelope, post-F1/F2 re-extraction 2026-07-30):
* Both functions: `args_unsupported: null`; `lo`/`hi` carry literal
  `default` payloads; `hi is None` is an in-tier `Compare [Is]`; the SOLE
  `Unsupported` node per function is the `raise ValueError` guard behind
  `if lo < 0` — unreachable at the default (`lo = 0`), so the two-argument
  theorems below cover the byte-verbatim body with its exception path
  intact (rsa_inverse precedent). The `#guard … matches .unsupported`
  lines document the edge: an explicit negative `lo` DOES reach the raise
  and the interpreter refuses loudly.
* Both loop bodies CREATE `mid` on the first iteration, so the loop
  tactics' v1 recipe does not apply — the proofs hand-instantiate the
  generic while rule (see proof.lean header and the growing-environment
  row of AGENTS.md's goal-shape table).

PROVENANCE OF THE PROOFS: benchmark cold-prover runs, 2026-07-30
(docs/benchmark.md "Cold-prover runs") — two independent agents, repo
docs only; adapted here with statements only strengthened (deltas in
docs/benchmark.md).

Non-vacuity gap (recorded per AGENTS.md): `harness/cases.json` rows are
inexpressible for these functions — `leanmodels-run` parses CLI args as
ints only, and `a` is a list. Fallback: the concrete CPython-checked runs
from the vendored docstring's authenticity block are stated as
`#py_check` lines below.

No `@[spec]` forms: the results are `takeWhile`-valued / relational, not
conditional-simp shapes (cf. Examples/python/rsa_inverse/spec.lean).
-/
import Examples.python.bench_bisect.proof

open LeanModels LeanModels.Python

load_program bench_bisect from "Examples/python/bench_bisect/bench_bisect.json"

/-! Non-vacuity: concrete runs in surface syntax (`#py_check`,
Surface.lean — fixed generous fuel). The two-argument rows exercise BOTH
defaults; the four-argument row exercises neither; values match the
authenticity block of bench_bisect.py (CPython 3.9.25, vendored file AND
installed C-accelerated module). -/
#py_check bench_bisect.bisect_left([1, 2, 2, 3], 2) = 1
#py_check bench_bisect.bisect_right([1, 2, 2, 3], 2) = 3
#py_check bench_bisect.bisect_right([1, 2, 2, 3], 5) = 4
#py_check bench_bisect.bisect_left([10, 20, 30], 25, 0, 3) = 2
#py_check bench_bisect.bisect_left(([] : List Int), 5) = 0
#py_check bench_bisect.bisect_right(([] : List Int), 5) = 0
#py_check bench_bisect.bisect_left([5, 7, 7, 9], 7) = 1
#py_check bench_bisect.bisect_right([5, 7, 7, 9], 7) = 3
#py_check bench_bisect.bisect_left([5, 7, 7, 9], 10) = 4
#py_check bench_bisect.bisect_left([5, 7, 7, 9], -3) = 0

/-! Tier-edge documentation: a NEGATIVE explicit `lo` reaches the vendored
`raise ValueError('lo must be non-negative')` — the single Unsupported
node per function — and the interpreter refuses loudly (`.unsupported`,
not a Python result). The theorems below never touch it: the default
`lo = 0` makes the guard concretely false. -/
#guard (callFunction bench_bisect "bisect_left"
    #[.list #[.int 1, .int 2, .int 3], .int 2, .int (-1)] 4096 matches .unsupported _)
#guard (callFunction bench_bisect "bisect_right"
    #[.list #[.int 1, .int 2, .int 3], .int 2, .int (-1)] 4096 matches .unsupported _)

/-! ## `bisect_left` -/

/-- **Unconditional termination.** On EVERY list — sorted or not —
`bisect_left(xs, x)` terminates and returns an index in `[0, len(xs)]`.
No hypothesis on `xs` at all. -/
theorem bisect_left_terminates (xs : List PyInt) (x : PyInt) :
    ∃ i : PyInt, bench_bisect.bisect_left(xs, x) ==> i ∧
      0 ≤ i ∧ i ≤ (xs.length : Int) := by proofs

/-- **Main theorem.** For every sorted list `xs` and every `x`, the real
CPython `bisect_left(xs, x)` — run through the deep-embedded interpreter,
with `lo`/`hi` taking their defaults — terminates and returns the length
of the strict-lower prefix of `xs`: the leftmost insertion point for `x`. -/
theorem bisect_left_sorted (xs : List PyInt) (x : PyInt)
    (hs : List.Pairwise (· ≤ ·) xs) :
    bench_bisect.bisect_left(xs, x) ==>
      (xs.takeWhile (fun v => decide (v < x))).length := by proofs

/-- **Docstring characterization** (the contract stated in `bisect_left`'s
own docstring): on sorted input, the returned index `i` is in range, all of
`a[:i]` is `< x`, and all of `a[i:]` is `≥ x`. Stated relationally against
any observed run (`⇓`). -/
theorem bisect_left_insertion_point (xs : List PyInt) (x : PyInt)
    (hs : List.Pairwise (· ≤ ·) xs) {i : PyInt}
    (h : bench_bisect.bisect_left(xs, x) ⇓ i) :
    0 ≤ i ∧ i ≤ (xs.length : Int) ∧
    (∀ j : Nat, (j : Int) < i → xs.getD j 0 < x) ∧
    (∀ j : Nat, i ≤ (j : Int) → j < xs.length → x ≤ xs.getD j 0) := by proofs

/-- **Strengthened partial correctness** (`~~>`): every run of
`bisect_left(xs, x)` on sorted `xs`, at every fuel, either times out or
returns exactly the insertion point — no exception, no `unsupported`, no
other value. Free from totality via fuel determinism. -/
theorem bisect_left_partial (xs : List PyInt) (x : PyInt)
    (hs : List.Pairwise (· ≤ ·) xs) :
    bench_bisect.bisect_left(xs, x) ~~>
      (xs.takeWhile (fun v => decide (v < x))).length := by proofs

/-! ## `bisect_right` -/

/-- **Unconditional termination.** On EVERY list — sorted or not —
`bisect_right(xs, x)` terminates and returns an index in `[0, len(xs)]`. -/
theorem bisect_right_terminates (xs : List PyInt) (x : PyInt) :
    ∃ i : PyInt, bench_bisect.bisect_right(xs, x) ==> i ∧
      0 ≤ i ∧ i ≤ (xs.length : Int) := by proofs

/-- **Total correctness, relational form** (the cold prover's verbatim
claim): on sorted input the returned index `i` is in range, everything
before `i` is `≤ x`, everything from `i` on is `> x` — CPython's own
docstring contract for `bisect_right`. -/
theorem bisect_right_total (xs : List PyInt) (x : PyInt)
    (hs : List.Pairwise (· ≤ ·) xs) :
    ∃ i : PyInt, bench_bisect.bisect_right(xs, x) ==> i ∧
      0 ≤ i ∧ i ≤ (xs.length : Int) ∧
      (∀ j : Int, 0 ≤ j → j < i → xs.getD j.toNat 0 ≤ x) ∧
      (∀ j : Int, i ≤ j → j < (xs.length : Int) → x < xs.getD j.toNat 0) := by proofs

/-- **Main theorem (deterministic form).** For every sorted list `xs` and
every `x`, `bisect_right(xs, x)` with `lo`/`hi` defaulted terminates and
returns the length of the weak prefix `xs.takeWhile (· ≤ x)` — the
rightmost insertion point (the count of elements `≤ x`). -/
theorem bisect_right_sorted (xs : List PyInt) (x : PyInt)
    (hs : List.Pairwise (· ≤ ·) xs) :
    bench_bisect.bisect_right(xs, x) ==>
      (xs.takeWhile (fun v => decide (v ≤ x))).length := by proofs

/-- **Docstring characterization** (`⇓`-relational): any observed result of
`bisect_right(xs, x)` on sorted input is in range, with all of `a[:i]`
`≤ x` and all of `a[i:]` `> x`. -/
theorem bisect_right_insertion_point (xs : List PyInt) (x : PyInt)
    (hs : List.Pairwise (· ≤ ·) xs) {i : PyInt}
    (h : bench_bisect.bisect_right(xs, x) ⇓ i) :
    0 ≤ i ∧ i ≤ (xs.length : Int) ∧
    (∀ j : Int, 0 ≤ j → j < i → xs.getD j.toNat 0 ≤ x) ∧
    (∀ j : Int, i ≤ j → j < (xs.length : Int) → x < xs.getD j.toNat 0) := by proofs

/-- **Strengthened partial correctness** (`~~>`): every run either times
out or returns exactly the rightmost insertion point. -/
theorem bisect_right_partial (xs : List PyInt) (x : PyInt)
    (hs : List.Pairwise (· ≤ ·) xs) :
    bench_bisect.bisect_right(xs, x) ~~>
      (xs.takeWhile (fun v => decide (v ≤ x))).length := by proofs
