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

---

## 2026-08-22-lean-tier-2 — M2 OBLIGATION CENSUS: 24 sorries are 3 missing DEFINITIONS, and two of the three are already being written by strangers

Thomas ruled the endgame **(b) CONSUME-AND-EXTEND** — *"no reason to copy
lean4lean; if we can reuse most of it that sounds good."* Option (d), the
trust-extension surface, stays registered as the companion after (b)'s first
milestone. The edition token **`Lean433`** is **RATIFIED** as the family's first
§1.1 law-3 exception: Lean has no editions, only releases, so the law's premise
is false here — recorded with its reasoning in charter §12.1.

M2's deliverable: `docs/lean4lean-obligation-census.md` +
`harness/lean4lean_obligation_census.py` + its JSON.

### The counting rule, and the delta is a finding

**138 raw / 113 real / 25 comment-only.** A raw grep overstates the load by
**22%**, concentrated in docstrings and commented-out attempts. The stripper
handles nested `/- /- -/ -/`, docstrings, line comments and escaped string
literals while preserving line numbers; 11-case `--selftest`, nesting included.

### All three M1 figures re-verified: two confirmed, one wrong

24 shipped sorries **CONFIRMED**; 89 experimental **CONFIRMED** (24+89=113); the
two-stub `Theory/Inductive.lean` **CONFIRMED verbatim**; partition line counts
identical. **"11 proj-related" was WRONG — it is 10.**

### The structural finding

**24 obligations are 3 definitional stubs + 21 theorems, and 14 of the 21 are
blocked by a stub.** `TrProj` is `def … := sorry` — the relation does not exist —
and it alone gates **11 of 21 (52%)**. The seven `TrProj.*` lemmas are not seven
hard proofs; they are statements about nothing. **Writing `TrProj` is a
definition task, not a proof task.**

### The dependency graph is SEMANTIC, not nominal

Two obligations that look independent by name are not, and only reading the
executables found it: `tryEtaStructCore.WF` builds `.proj` terms directly;
`reduceRecursor.WF` reaches `.proj` **transitively**, two call hops away via
`toCtorWhenK → expandEtaStruct`. A name-prefix analysis put a blocked theorem at
the top of the candidate list. Both edges are now declared in the instrument with
the reasoning attached.

The corner table also found a bug in itself: a path-based classifier filed all
seven `TrProj.*` lemmas as "other" because they live in a generically-named file,
making the census's largest cluster invisible in its own summary. Name rules now
run first.

### The active-work split changes the plan

**DO NOT ENTER:** inductive types (open PR #43 replaces both stubs), `addDecl`
surroundings (PR #32, updated the day of the census), injectivity, universe
levels (11 commits on one day this month), church-rosser.

**UNTOUCHED, ranked:** (1) **`TrProj`** — no branch, no PR, no issue; `sorry`
~15 months; dependent lemmas from 2023. (2) `isDefEqUnitLike.WF` /
`tryEtaStructCore.WF` — 11 months idle, *partly* gated on (1), and this census
says precisely which half: `isDefEqUnitLike` is free, `tryEtaStructCore` is not.

**THE CHARTER'S "SEAM" CLAIM IS NOW STALE.** M1 §6.4 called
`Theory/Inductive.lean` the highest-value unwritten artifact in the field; three
weeks later there is an open PR filling it. A lane that had started there on the
charter alone would have duplicated a stranger's work. That is the argument for
running the activity check *before* choosing a target.

### The injectivity trap — a stale docstring nearly set our direction

M1 quoted `Injectivity.lean`'s *"theorems which we can't prove :("* and concluded
these were hard-and-avoid. **Wrong: injectivity is already proved sorry-free on
master**, for the `SExpr` development — and `Theory/`/`Verify/` contain **zero**
`import Lean4Lean.Experimental`. The open work is the SExpr→VExpr port, which is
the author's obvious next move. The right conclusion (avoid) survives; the reason
was wrong and the header predates the proof.

Related measurement hazard: the `logrel` branch reports 42 commits "ahead" but
was **rebased onto master with new SHAs**. **A branch-ahead count is not evidence
of unmerged work here**, and every "untouched" verdict inherits that caveat.

### Two traps recorded for any future run

**`sorry` → `axiom` laundering:** the `types2025` branch converts eight sorries
into `axiom`s with `-- := sorry` kept as a comment — zero proof content. A
sorry-counter run there would report an improvement that did not happen. This
instrument counts axioms alongside sorries for exactly that reason.
**Recency that discharges nothing:** several sorry-bearing files show August
dates from toolchain bumps and a namespace move; the *site* blame is the honest
signal, and several are from 2023.

### Candidate first proof

**`isDefEqUnitLike.WF`** — the independent half of the second-ranked untouched
cluster: 9-line subject, no proj dependency (verified directly and
transitively), one waiting consumer in the same file, 26 proved analogues around
it at a median of 15 lines, and it realises `unit-like`, one of the 16 named
kernel rules in `docs/lean-kernel-census.json`. `checkPrimitiveDef.WF` was
**disqualified mid-census** when the activity data showed PR #32 touching it.

### Governance, for the engagement decision

Nine external proof PRs unanswered; one maintainer reply across eleven; no
published open-problems list; and **Thomas's own issue #16 — asking exactly which
sorries are unclaimed — open 23 days with zero replies.** No contact was made by
this census; engagement remains Thomas's call.

### Discipline

No Lean run, no build, no ticket. M1 inch 2 already built this commit green in
98 s and that is cited rather than repeated. Public reading only. Deferred items
unchanged: Mathlib export blocked; inch-6 gate over our own `.olean`s awaits a
quiet machine.

---

## 2026-08-22-lean-tier-3 — M3 inch 1 WITHDRAWN: the candidate first proof is blocked on a MISSING MODEL RULE, and my own M2 census recommended it

M3 was ranked: (1) prove `isDefEqUnitLike.WF`, (2) `TrProj` the definition. **Inch
1 is not available, and the census that recommended it was wrong.** No proof was
forced and no trusted definition was quietly extended to make one go through.

### The measurement

`isDefEqUnitLike.WF` must conclude that two arbitrary inhabitants of a unit-like
inductive are definitionally equal. **`VEnv.IsDefEq` has 13 constructors and none
of them can conclude that.** Walked individually: `eta` is *function* eta;
`proofIrrel` requires `.sort .zero` so it only reaches `Prop`; `extra` admits
only what `env.defeqs` carries, and that is populated from exactly two checked
places — δ-unfolding (`Theory/Typing/Env.lean:15-16,26,31`) and the quotient
package (`Theory/Quot.lean:21`). No lemma in `Theory/` concludes defeq of two
arbitrary inhabitants.

Cross-checked against this tier's own M1 instruments, which is what makes it firm:

| source | unit-like rule? |
| --- | --- |
| C++ kernel (`lean-kernel-census.json`) | **YES** — `is_def_eq_unit_like`, and separately `try_eta_struct_core` |
| the thesis (`lean-spec-census.json`) | **NO** — names only β, δ, η, ι, ζ |
| lean4lean's model | **NO** — 13 constructors |

**These are SPEC-GAP obligations, not proof obligations.** The rule exists in the
kernel, is absent from the 2019 spec, and is absent from the model that mirrors
that spec. Proving the theorem requires first *adding a rule to the model* — a
change to a trusted definition. That is why both `IsDefEq.lean` sorries have
stood eleven months with no claimant, and it is a better explanation than
"nobody got round to it".

### The method error, and it is mine

M2 introduced the semantic-dependency lesson and then committed a second instance
of it. My dependency check asked *"does the executable touch `proj`?"* — about
the **implementation**. It never asked *"does the model contain a rule that could
make this theorem true?"* — about the **specification**. Corrected triage rule,
now in the census: check **(a)** is the definition it needs present, **(b)** does
its executable reach a blocked construct directly or transitively, **(c)** can
the model discharge its conclusion at all. **(c) is the cheapest of the three and
it eliminated two candidates instantly.**

### Consequence: every independent obligation is unavailable

Injectivity ×3 and `NormalEq.parRed` ×2 and `checkPrimitiveDef.WF` are all DO NOT
ENTER (author's port; the `.extra` case circled by his own work and PR #43; PR
#32 updated the day of the census). `isDefEqUnitLike.WF` is blocked on the
missing rule; `tryEtaStructCore.WF` is blocked twice, on that **and** on `TrProj`.

There is no available first proof of the shape M2 proposed. Forcing one would
mean racing the author or quietly extending a trusted definition. Both refused.
**This promotes inch 2 from "highest-leverage" to "the only available item"** —
which is where the ruling already pointed.

### Inch 2 — the `TrProj` design census (census-first, not started)

What must be matched, from the kernel: `reduceProjCore` selects
`args[numParams + i]` from a constructor application; `inferProj` walks the
constructor telescope instantiating **earlier fields as `proj I j s`** (dependent
projections) and enforces the `Prop`-squashing side condition **twice**.

What the thesis offers: **nothing.** `proj` is absent from its 7-form grammar and
from all 71 kernel-relevant rules. So "match both sources" resolves
asymmetrically — design against the kernel, then write it *as the rule the thesis
would have had* so it can be cited into the §7.4 correspondence manifest.

`VExpr` has 6 constructors and no `proj`, so the projection must be **encoded**.
Three candidates, two rejected with reasons: **(a) recursor encoding — REJECTED**,
it needs `VInductDecl.WF`/`addInduct`, i.e. PR #43's territory, which the ruling
excludes; **(b) projection-constant encoding — REJECTED**, those are derived
declarations that need not exist, and `proj` is primitive precisely to avoid
them; **(c) reduction-relational — RECOMMENDED**, mirrors `reduceProjCore` and
`inferProj` and stays clear of both live PRs.

**The crux, and it is where the kernel is unsound.** The hard case is a STUCK
projection, and `proj-of-stuck-prop` / `proj-of-subst-prop` are two of the four
arena soundness tests **our own pinned kernel fails**. So `TrProj`'s hardest case
is the case the reference implementation gets wrong, and the design question —
model what the kernel *does*, or what it *should do*? — has to be settled before
any code. §4.2's precedence rule answers it (state the rule, record the oracle's
behaviour, publish the divergence), but this is the first time in this tier that
rule has teeth.

### Hygiene

No PRs, no comments, no contact upstream — engagement remains Thomas's call and
he has personal standing via issue #16. Work stays in our own clone. The
axiom-counting rule is now in the instrument's docstring **as the trap it
prevents**, with the measured `types2025` evidence: eight sorries converted to
`axiom`s with `-- := sorry` kept as a comment, zero proof content — a
sorry-counter run there reports an improvement that did not happen.

No Lean run, no build, no ticket taken this dispatch: the finding is a source
measurement, and the C++ kernel side was taken from our own committed
`lean-kernel-census.json` rather than re-fetching a wiped corpus.
