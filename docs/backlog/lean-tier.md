# Lean tier — lane backlog

Per-lane file per `docs/family-architecture.md` §9.5. Ids are
`YYYY-MM-DD-lean-tier-<n>` and need no reservation. Landings before this file
existed are in the archive as §L79 (founding charter) and §L85 (M1 complete).

---

## 2026-08-22-lean-tier-1 — §9.1 audited against this lane's six instruments; the one real defect was found twice, and the audit lane landed first

The standing strategy's **BUG BEFORE REFACTOR** clause, run against this lane's
six instruments. Two defects are named in §9.1. This lane had exactly one of
them, in exactly one instrument — and **found it independently of, and slightly
later than, the audit lane, which had already fixed it.**

### The `--compare` exit-0-on-drift bug: NOT PRESENT here

§9.1 names `c_construct_census`, `wasm_spec_census` and `wasm_suite_census`.
None of this lane's instruments is on that list, and the absence was **verified
rather than assumed**:

* all five `--compare` implementations return `1` on drift and `2` on a missing
  baseline — audited by reading every return path;
* `lean_rule_correspondence.py` was **run**: clean compare exit 0; perturbed
  baseline → `DRIFT: thesis_kernel_rules`, exit **1**.

The other four could not be re-run this dispatch — two need corpora a harness
restart destroyed (the C++ kernel checkout and the thesis clone), and two invoke
Lean, which amendment 11 puts behind a ticket. Their drift paths were exercised
when they landed; this is that record, not a fresh run, and it is stated as such.

**Independently corroborated:** the audit lane's own fix commit touched
`c_construct_census`, `es_census`, `wasm_spec_census`, `wasm_suite_census` and
one file of this lane's — and **left the other five of ours alone**. Two audits
from different directions agree on which instruments were clean.

### The `git_rev`-swallow bug: PRESENT in `lean_independent_check.py` — and FIXED UPSTREAM, not here

§9.1's second defect — *"copies of a 6-line `git_rev` that all swallow their
failure and stamp `null` provenance"* — had an instance in this lane's
`lean_independent_check.py`:

```python
rev = ""
try:  ... git rev-parse ...
except (OSError, subprocess.SubprocessError):
    pass
```

An `except: pass` stamping an empty `checker_commit`. A direct breach of the
never-hide-errors law, and **worse in this instrument than in most**, because the
artifact's entire claim is *"checker X accepted these modules"*. A verdict file
that cannot say **which X** is not weak evidence — it is no evidence.

**This lane wrote a fix and then discarded it.** The audit lane had already
landed one in `28b9f5e`, and on rebase the two collided. Theirs is semantically
identical and **strictly better written**: it folds the empty-output case into
the same condition and surfaces git's own stderr, so the refusal reads
`(exit 128): fatal: not a git repository` instead of a bare assertion that the
directory is not a checkout. Taking ours would have been churn on top of a
landed, tested fix.

**What this lane contributed instead is verification**, re-run against their
version: a non-git directory carrying a fake `lean4lean` binary exits **2**, and
the check sits above the module loop, so **no checker process is ever spawned** —
the refusal costs nothing and cannot half-run.

**Output is byte-identical for a valid checkout** (§9.2's test), shown without a
Lean run: the real checkout's `git rev-parse` and the committed
`docs/lean-independent-check.json` both read `e0e3f6bcccb8`. The fix changes
behaviour only where there was no provenance to record.

**One detail worth keeping.** This lane's other three git helpers already raised.
The defect was in the **newest** of the six, written last and fastest — the
ordinary shape of this failure, and a concrete argument for the shared helper
§9.1 asks for, since the defect reappears per-copy rather than persisting in one
place.

### Adoption status for the rest of §9

* **`harness/censuskit.py`** — not in the tree yet; nothing to adopt. Per §9.2
  this lane converts **on next touch** of each instrument, with the
  byte-identical test.
* **`tools/triad.sh`** — adopted for any future build. Noted: its header
  **recovered amendment 8**, which the prose register had lost — the audit's
  script-beats-prose thesis demonstrated on the register itself.
* **Amendment 13 CoW seeding** — adopted for the next workspace. This lane paid
  the cost A13 removes in full this dispatch, re-cloning from scratch after a
  harness restart destroyed its tree.
* **Per-lane backlog** — this file. `docs/backlog.md` untouched; converting it to
  a generated index belongs to the migration commit, not to a lane's landing.

### Deferred, unchanged

**Mathlib export: BLOCKED** — needs the coordinator's sign-off and Thomas's
training finished. §5's own pricing already said peak RAM is the binding
constraint, which is exactly what the 3 GB RSS line governs. **Inch-6 gate over
our own `.olean`s: awaits a quiet machine** — a ~3 700-job build that would hold
the machine's entire Lean allowance.

No Lean run, no build, no ticket taken for this landing.
