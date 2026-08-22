# The PROOF-WRITER QoL lane's backlog

Per-lane backlog, per `docs/family-architecture.md` §9.5. **Appended only by
the QoL lane.** Ids are `YYYY-MM-DD-qol-<n>` and need no reservation, because
the lane name makes them unique.

This lane writes **no Lean and runs none** (A11). Its subject is the cost a
proof writer pays between having an idea and having a green: the log they
cannot read, the statement shape they get wrong for the fourth time, the law
they cannot find, and the full build they did not owe. Everything here is
mined from the repository's own record — **every tool entry cites the
incident that minted it**, because a decoder that guesses is one more thing
to distrust.

---

## 2026-08-22-qol-1 — `tools/triad.sh --classify`: the triad now sizes itself to the diff, and SAYS WHAT ITS GREEN COVERS

Base rule 4 says *one triad per landing*. It does not say every landing owes
the same triad. A docs-only landing that pays for a full build pays a tenure
the machine does not owe it — and A11 makes tenures scarce on purpose, since
the lock covers **all** Lean execution and Thomas's own processes outrank
every lane.

But the reason this is a `--classify` flag on the canonical wrapper rather
than a lane's private shortcut is the other half: **a scoped green that does
not say what it covers is §5.4a's exact failure mode** — a number quoted
without the state it was taken in. So the classification is not only a
scope-picker; it prints the coverage statement next to the verdict, and the
triad repeats it at the end.

### The three classes, and where each boundary comes from

| class | what it is | build | tenure |
| --- | --- | --- | --- |
| `docs` | nothing in the diff can reach the elaborator | none | **no** |
| `tier` | `LeanModels/<tier>/` and its `Examples/` | scoped `lake build <modules>` | yes |
| `spine` | `LeanModels.lean`, `LeanModels/Core/`, the shared harness, the lakefile — **and anything unrecognized** | full | yes |

`docs` owes no tenure because `tools/docs_check.py` **shells out to nothing**
— checked, not assumed — so there is no Lean process for A11's lock to
cover. `harness/diff_test.py` runs `lake build` and `lake exe`, so any class
that runs it takes a tenure. That is the whole rule: the tenure follows the
Lean, not the file count.

`harness/diff_test.py` and `harness/cases.json` classify as **spine**, not as
tooling: they are the differential every tier is judged by. The other
`harness/*.py` are lane instruments — changing one invalidates no `olean`,
so they are `docs`, and a lane that wants its instrument exercised passes
`--gates`, which brings the tenure back.

### The direction of every doubt is fixed, and lean-tier paid for the rule

An unrecognized path **escalates and is named**. `docs/backlog/lean-tier.md`
§`2026-08-22-lean-tier-2` minted this the expensive way: a path-based
classifier filed all seven `TrProj.*` lemmas as *"other"* because they lived
in a generically-named file, and **the census's largest cluster went
invisible in its own summary.** A classifier that absorbs what it does not
recognize produces a confident wrong answer; this one prints
`UNKNOWN <path> <- no path rule matched; escalated, not absorbed`.

The same asymmetry decides the `Examples` module names. `Examples/system-verilog/toggle/proof.lean`
is really `Examples.«system-verilog».toggle.proof`, and the guillemets are
in the source imports — but whether that spelling survives the `lake build`
command line is something this script would have to **run Lean** to find out,
which A11 forbids. So a hyphenated example directory widens to the
`Examples` library target: less scope, **zero invention**.

### Never downgrade, stated as code

* the classification is a **floor**: `--gates` from the lane is appended to
  the floor, never substituted for it, and it re-arms the tenure even in the
  `docs` class;
* `BUILD_TARGETS` is only ever added to (`add_build_target` is a union), so
  a future `--build-target` flag composes with the classifier instead of
  fighting it;
* a `LeanModels/` path whose module name cannot be derived **escalates the
  whole landing to a full build** rather than silently building less;
* an **empty** diff is not a docs-only landing. It is a classification that
  measured nothing, and it says so and falls back to the full build — the
  silent-0-line-census law pointed at the classifier itself.

### The merge target carries its own provenance

The default base is `github/master`, falling back to `origin/master`, and
the chosen ref, its sha **and its remote URL** are printed. If that URL is a
local path or a bundle, the run prints the **A13 caveat** loudly: a seeded
clone inherits the peer's remotes, `origin` can be a stale local bundle from
2026-08-14, and `git rev-list HEAD..origin/master` reports `0` because it is
comparing against the bundle. Four lanes, one root cause (§7.1a). The run
also counts **unstaged `.lean` files it did not classify** and says so —
they are not in this green.

### Triad

`bash -n` clean. `--self-test`: **42 ok, 0 failed** (12 pre-existing queue
and lock checks unchanged, **30 new**), covering all three classes, both
mixed diffs (docs+tier → `tier`; docs+tier+spine → `spine`), two tiers in
one diff, the unrecognized path, the underivable module, the `input_dir`
file that is a real build input, the rootless tier (`Sv` has no
`LeanModels/Sv.lean`), and the never-downgrade rule. The four live classes
were exercised with `--classify-only`, which takes **no tenure and runs no
Lean**. **No Lean was executed by this lane at any point.**

---

## 2026-08-22-qol-2 — `docs/statement-cookbook.md`: 21 claim shapes, each with the incident that minted it

A proof that closes is not the same as a claim that means something, and this
repository has the receipts: `BoundRefines` **refuted** at every depth for
every value function (§L26); a fuel numeral in a *hypothesis* that made a
whole chain vacuous (§L24); a `⊕` at a membership site that would have
silently converted a **permission into an obligation** and made every Ada
verdict a falsehood (`docs/proof-framework-research.md` §5.4). None of those
announced themselves — §0.1 II(a) is why: a failed *statement* prints *"does
not depend on any axioms"*, **cleaner than the truth**.

So the cookbook is a record, not advice. **One page per shape: the canonical
form, the trap, and the real incident that minted it**, cited to a durable
home. 21 entries: the ten shapes the lane was dispatched with, plus eleven
more found in the same sweep — well-formedness premises, partial correctness,
short-circuit out-worlds, residue spelling, existentials, read-only framing,
statability under `rfl` vs `#guard`, refinement's ∀∃, the refusal-cause
quantifier flip, invariant altitude, and the re-proving discipline.

### Two things it deliberately does NOT contain

**Totality** and **decidability-in-statements** are listed as **empty rows**.
Both were searched for and neither has a minting incident: totality appears
only as the total judgment subsuming the partial one by monotonicity, and the
decide-ladder is a *tactic and trust* policy, not a statement shape. An entry
gets written when an incident mints it; **until then the honest thing is an
empty row, not a plausible rule.** This is §5.3's *VACUOUS is not a verdict*
pointed at a document.

### One correction to the dispatch

There is **no `docs/python-refounding-plan.md`** in the tree, at any path —
the re-founding material lives in `docs/backlog/sunfish-rtrack.md` (entries
`-3` and `-4`) and in `docs/backlog.md`'s *"THE SPEC/INTERPRETER SPLIT HAS A
PRICE TAG"*. The 65% law is mined from those. Recorded rather than quietly
worked around, because a pointer to a durable home is not a durable home
(§7.1a).

### Triad

Docs-only landing, and it was classified by the tool that landed an hour
before it: `tools/triad.sh --classify-only` reports **`docs`**, builds
nothing, takes **no tenure**, and owes exactly `python3 tools/docs_check.py`
— which passes: **83 marked blocks (83 ok), 29 illustrative-exempt**. The
Lean sketches in the cookbook carry no path markers, so they are
`illustrative` by the marker convention rather than checked against a tree
they do not live in. **No Lean was executed.**

---

## 2026-08-22-qol-3 — `tools/diagnose.sh`: 22 failure signatures, each with the incident that minted it

The expensive part of a red is almost never the red. A stale `olean` cost one
lane **roughly two hours and survived four plausible diagnoses** (§L62). A
torn-tree rebase cost the Go lane a hunt for four constants that were on
master all along (§7.2). Every one of those has a **literal string in the
log**, and every one is written down in this repository — just not next to
the log. The decoder puts the record next to the log: give it a build or
elaboration log (file or stdin) and it annotates the lines it recognizes with
**CAUSE, FIX, and THE LAW'S HOME**.

The home is the point. An annotation with a pointer can be checked, and it
does not become the fourteenth copy of a rule — which is the defect
`docs/duplication-audit.md` measured across the census contract.

### The signature set, and what it is worth

22 signatures. The ones that pay for the tool are the ones that **read
cleaner than the truth**, per §5.4a:

* `axioms-clean-lie` — *"does not depend on any axioms"* printed for a
  declaration whose **STATEMENT** failed. §0.1 II(a)'s mode table is carried
  in the annotation: three failure modes print `[sorryAx]` honestly and only
  the fourth lies.
* `whnf-timeout` — **four** distinct recorded causes wear this one face, so
  the annotation is a *discriminator ladder*, cheapest first: `#check @thm`
  (the two-hour stale-olean case), then a fresh abstract frame, then symbolic
  fuel, then altitude lemmas — **the budget knob is the wrong knob.**
* `unknown-constant` — a torn tree or a stale olean, never evidence that
  master is broken. It discharges nothing and convicts nothing.
* `resource-kill` (137/143), `unknown-option`, and the whole-log verdict
  `build-did-not-happen` — the three ways a log can carry **no line the
  failure greps look for**, which is why the tool asserts success
  **positively** and says so when neither a success line nor an error line is
  present.

The rest: `mvcgen-bare-false` (the splitter dropped the discriminant — and
`+jp` may be the source of the lossiness rather than its cure),
`lock-release-failed`, `worker-sigtrap`, `omega-no-constraints` (ascription
does **not** unbrand, and the restated hypothesis prints identically — *no
visible difference is the tell*), `max-rec-depth` (three causes, and raising
the option is right for exactly one), `vacuous-match`, `kernel-type-mismatch`,
`doc-comment-before-command`, `universe-metavariables`, `split-failed`,
`spec-proof-twin`, `py-loop-context`, `sorry-warning`, `census-drift`,
`null-provenance`, `queue-gave-up`, `seeded-clone-identity`.

### One signature the dispatch asked for is NOT here

**`E999` on a generated artifact does not exist in this repository.** It was
searched for properly before being dropped: `grep` over the working tree,
`git log -S` and `-G` over all branches, and a `git grep` sweep over 400
revisions — **zero hits at any revision** — and the repo has no numbered-code
linter that could emit one (`docs_check.py` and `es_lean_lint.py` are the
only linters, and neither emits `E`-codes). Recorded as an empty row rather
than shipped as a plausible rule: a decoder that guesses is one more thing to
distrust.

### Honest misses are LOUD

When nothing matches, the tool says so and refuses to be read as a clean
bill: *"A decoder that says nothing must not be read as a decoder that found
nothing wrong."* That is §5.3's *VACUOUS is not a verdict* pointed at this
instrument, and it is the reason the no-match branch is in the self-test.

### Triad

`bash -n` clean. `--self-test`: **51 ok, 0 failed** — **every one of the 22
signatures EXECUTED against its own fixture** through the same matcher the
live path uses (a fixture is the real log line wherever the record quoted
one), plus a completeness check that each carries all four annotation fields,
a benign progress line that must fire **nothing**, a green log, the silent-log
whole-log verdict, and a multi-line count that must not dedupe. Live path
exercised on a mixed log, a green log, an unrecognized error, `--list`,
`--explain` and its refusal. **No Lean was executed** — the tool reads text,
so it is safe outside a tenure (A11).

---

## 2026-08-22-qol-4 — `docs/law-index.md`: 315 laws, and every one is a POINTER

The page a lane loads at session start. **315 rows across five buckets** —
measurement 63, statement 100, proof-engineering 55, build+ops 64,
clone-identity 33 — swept from `docs/family-architecture.md` (including the
§7.1a register), `AGENTS.md`, every `docs/backlog/<lane>.md`, the `§Lnn`
archive, `docs/duplication-audit.md`, and the three scripts that carry laws
as code (`tools/triad.sh`, `tools/ci.sh`, `tools/docs_check.py`).

**It restates nothing.** Each row is a hook phrase — the project's own words
wherever possible — and a pointer to the durable home. That is not modesty,
it is §7.1a's lesson applied to itself: a summary would be a fourteenth copy
of each rule, which is exactly the defect `docs/duplication-audit.md`
measured across the census contract. Read the law where it lives; use this
page to find it.

### The index's own ids are NOT amendment numbers

`MEAS-`, `STMT-`, `PROOF-`, `OPS-`, `CLONE-`. A second `A1..An` numbering
over the same letters would collide with §7.1a's amendments — `A4` already
means "the owner file is written once under `set -C`" — and a citation trap
in the index of citations is the last place it belongs.

### Three traps in the citations themselves, recorded on the page

1. **Two register rows are LOST at source.** §7.1a carries no recovered text
   for amendments 1 and 3. Any claim that the protocol is fully written down
   is **false by the register's own admission**, and the index says so rather
   than quietly listing eleven amendments as though they were thirteen.
2. **`docs/backlog.md`'s bare "law N" numbering has drifted** — §L41 records
   *"the FIFTH renumber this lane has taken today"*, and later entries cite a
   "law 5" of an entry whose own list has three. Cite by the `§Lnn` that
   houses the law, never by a bare law number.
3. **`§5.1`/`§5.2` resolve differently depending on which file you stand in**:
   `docs/duplication-audit.md` has its own, unrelated to the family doc's.
   Always carry the filename — the same collision class the audit flagged for
   `L2`/`L3`/`L4`.

### The one rule the index adds

**Append the row when you append the backlog entry, in the same landing.** An
index a lane has to remember to update is an index that goes stale, and a
pointer to a durable home is not a durable home.

### Triad

Docs-only landing: `--classify-only` reports `docs`, no build, no tenure,
`python3 tools/docs_check.py` green (**83 marked blocks, 83 ok**). Every
cited per-lane backlog id was verified to resolve in the tree at push time
(`es-1`, `c-1`, `ada-1`, `sv-1`, `sunfish-rtrack-4/-5`, `lean-tier-2/-4`,
`wasm-1`, `research-1`), and the family-doc subsection numbers were checked
against the heading list rather than remembered — §5.4a's retrieval clause:
**a grep that agrees with your prior is the one to re-run.** No Lean was
executed.

---

## 2026-08-22-qol-5 — `--classify` reachability: the Go lane's correction, and the measurement that widened it

The Go lane measured a hole in `2026-08-22-qol-1`'s `Examples/*` rule:
`Examples/go/pipeline/pipeline.go` classified **tier** although it is
*provably invisible to lake* — nothing imports it, the `Examples` glob
matches Lean **module** names, and a `.go` file has none. Their reasoning is
right and the fix is theirs: **the distinguishing property is not the
extension, it is REACHABILITY.** `Examples/c/sunfish/sunfish.json` must stay
tier-local because a `.lean` ingests it.

### The measurement widened the referencing set, and this is the finding

Implemented verbatim — `git grep` the path and basename across `*.lean` — the
rule was **measured against all 200 non-Lean fixtures in the tree before it
landed**: 121 referenced, **79 unreferenced**. But **40 of those 79 are
`Examples/python/**` fixtures named by `harness/cases.json`**, which is
exactly what `harness/diff_test.py` reads. Downgrading them to `docs` would
have **skipped the differential for a change that is an input to it** — a
real downgrade, and the law the classifier is built around forbids it.

So the referencing set is *what runs under the tenure*: **the Lean modules
AND the gate corpora**. With both: **160 reachable, 40 provably invisible** —
the `.go` case among them, alongside a README, the ingested-then-committed
envelopes, and the SV `sem2` probe corpus.

Order of rules, strongest evidence first: a `.lean` is tier without a probe;
a lakefile **`[[input_dir]]`** member (`Examples/spice/*.cir`,
`Examples/verilog-a/*.va|*.json`) is tier without a probe, because that is a
fact of `lakefile.toml` and not a heuristic; everything else is probed. A
downgraded fixture contributes **no tier and no build target**, and the
classification line **says why** — so the §5.4a statement carries the
reasoning, not just the verdict.

### The self-test caught a defect in the doubt direction

Doubt was supposed to resolve to *reachable* via grep's error status. Pointed
at an unreadable root, **this grep exits 1 — "not found" — where the same
grep exits 2 for a bare missing operand.** "The probe could not run" is
therefore **indistinguishable from "nothing references it" by status alone**,
and trusting the code would have silently downgraded every fixture whenever
the root was wrong. The doubt test is now **structural** — the root must be a
readable directory before any status is believed. That is §7.1 rule 5's
lesson in another costume: *a broken liveness check does not fall back to
caution, it falls FORWARD.*

### Triad

`bash -n` clean. `--self-test`: **54 ok, 0 failed** (42 → 54, **12 new**): a
referenced fixture (a `.lean` names it) → tier and owes the `Examples`
library; a gate-corpus fixture → tier; an unreferenced one → docs with no
tier, no target, and the line that says why; a `.lean` under `Examples` and an
`input_dir` member → tier **without** a probe; mixed invisible+reachable →
tier scoped to the reachable one; and DOUBT → tier. The probe's two
directions run against a real fixture tree built by the test, so both the
`git grep` and plain-`grep` paths are exercised. Verified live on all three
real cases: `pipeline.go` → **docs**, `sunfish.json` → **tier C**,
`exc_lab.py` (named only by `cases.json`) → **tier Python**. Tools-only
change: **no tenure, no Lean executed** — this lane's own rule, applied to
this lane.
