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

---

## 2026-08-22-qol-6 — the DEFAULT GATE SET now announces itself: the ES lane's migration finding, made loud

The ES lane found this **by reading its own log rather than trusting it**:
`tools/triad.sh`'s default gates are `docs_check; diff_test`, and
**`script_corpus` is not among them** — though the `es-build.sh` it retired
ran all three. The default is not wrong (gates are a lane's business, and the
script takes `--gates`), but **a lane migrating to the shared wrapper
inherits a narrower gate set silently**, and the failure mode is *a landing
that reads green against fewer checks than the one before it*
(`docs/backlog/es.md 2026-08-22-es-1`).

That lane also wrote the sentence that decides the fix: **"which no amount of
care at the build itself would catch."** A missing gate leaves no trace in the
log — the run is green *and correct*. There is nothing to detect. So it is
not caught, it is **ANNOUNCED**.

### What lands

Every run that did **not** choose its own gates now prints, before running
them:

```
  !! DEFAULT GATES: docs_check, diff_test (minimal).  A lane migrating from a
     private script should pass --gates matching what it RETIRED.
     es-build.sh also ran script_corpus; a lane that retires its script and
     takes this default lands GREEN AGAINST FEWER CHECKS THAN THE ONE
     BEFORE IT — which no amount of care at the build itself would catch.
     (docs/backlog/es.md 2026-08-22-es-1)
```

A lane that passed `--gates` gets **nothing** — it already chose, and a
warning it cannot act on is noise. The notice fires **once per run**, on all
three paths that run gates (the normal tenure, the docs-only no-tenure path,
and the classification report). `--classify` additionally states its floor in
the same short-name style — `gate set  docs_check, diff_test   (the CLASS
FLOOR for `tier`)` — so the class's full list is legible next to the coverage
statement rather than only as a shell command line.

### It is deliberately NOT a diagnose.sh signature

`tools/diagnose.sh` now names it under **"FAILURES WITH NO LINE TO MATCH"**,
alongside the build that never ran. The distinction is worth keeping sharp:
the build that never ran is still catchable as a **whole-log verdict**,
because "no success line and no error lines" is a property of the log.
Green-against-fewer-checks is not — the log is green, correct, and carries no
baseline. The only string a decoder could match is `triad.sh`'s own notice,
and a signature matching that would **restate the notice**: a second copy of
one rule, which is the defect `docs/duplication-audit.md` measured. **A
signature that cannot fire on the failure is not a signature.**

### Triad

`bash -n` clean on both scripts. `tools/triad.sh --self-test`: **61 ok, 0
failed** (54 → 61, **7 new**) — gate names read as script names, the docs
floor names one gate, a default invocation warns, names what to do, and cites
the incident; a lane's own `--gates` does **not** warn; and the notice prints
**once** per run. `tools/diagnose.sh --self-test`: **51 ok, 0 failed**,
unchanged (a comment, not a signature). Live: exercised on a tier diff with
and without `--gates`, and end-to-end on a real **docs-only landing** — notice
printed once, `docs_check` green 83/83, **no tenure taken**. Tools-only
change: **no Lean executed**.

---

## 2026-08-22-qol-7 — `tools/check.sh`: rule 3's warm-clone amendment, CHECKED instead of guessed

The edit-check loop is the proof writer's inner loop, and §7.1 rule 3 allows
exactly one cheap form of it — `lake env lean` on a small file, without the
lock. Then the rule amends itself, because a lane got it wrong in the obvious
way: **"AND ONLY IN A WARM CLONE — the exemption is a property of the CLONE,
not of the file."** In a cold clone the same command resolves and downloads
dependencies: Lean execution outside the lock (**A11**) and a GB-scale
download instead of CoW seeding (**A13**).

**A rule whose precondition cannot be seen is a rule that gets guessed.** So
the script does not ask the lane to know whether the clone is warm — it
checks, names the case, and refuses when the case is not one rule 3 covers.
It always prints which of three cases it is in:

| case | meaning |
| --- | --- |
| `tenure` | the lock owner's pid **is us or an ancestor** — we are inside a ticket |
| `scratch` | outside every lake glob **and** every project import has an olean |
| `refuse-library` | inside a lake glob — that is the build's own graph; take a ticket |
| `refuse-cold` | an import has no olean — seed first (A13), then probe |

Two details that are laws rather than choices. **The lake libraries are READ
FROM `lakefile.toml`**, not hardcoded — a hardcoded glob is a second copy of
the lakefile that goes stale silently, and this lane already shipped one
classifier that had to learn that (`qol-5`). And **ownership is decided by
process ANCESTRY, not by matching a lane tag**: A4's corollary is that the
owner file is a *hint* and the process tree is the truth, so a stale owner
file cannot talk this script into running.

Core modules (`Init`, `Std`, `Lean`, `Lake`) are deliberately **not**
olean-checked: probing them would mean starting a Lean process to ask where
they live, which is the thing the script exists to gate.

### Verified by its refusals, and that is the honest boundary

`--self-test`: **26 ok, 0 failed**, against a fake clone built with the real
one's shape — the lakefile's libs are read not hardcoded, all four glob
classes, import parsing, guillemet stripping, package oleans, core imports
exempt, and every one of the four verdicts including a tenure that outranks
both refusals, another lane's lock, an unparseable owner, and no lock at all.

Live on this clone — which has **no `.lake` at all** — the tool **refused
twice**: `LeanModels/Core/Basic.lean` → `refuse-library`,
`docs/mvcgen-pilot.lean` → `refuse-cold` naming the missing import. Its happy
path executes `lake env lean` and was therefore **not run**: this lane holds
no ticket, and `--explain` prints the exact command instead. That boundary is
stated rather than papered over — **the refusal paths are RUN; the execution
path is the one thing a no-Lean lane cannot certify.**

---

## 2026-08-22-qol-8 — `tools/new-proof.sh` and `tools/analogues.sh`: the laws at the moment they are cheap

### `new-proof.sh <kind> <name>` — four scaffolds, laws inline

Four shapes recur, and each has a trap a lane rediscovers expensively:
`BoundRefines` **refuted** at every depth for every value function (§L26); a
fuel numeral in a hypothesis making a chain **vacuous** twice over (§L24); a
joined `FoldInv` nearly shipped as a headline while being about **3.5% of
cuts** (`2026-08-22-sunfish-rtrack-4`). None announced themselves. So the laws
travel **with the shape, at the moment the statement is written** — the only
moment they are cheap. `gate` carries the exit law, *measure before you
premise*, the same-commit consumer, and *record the `jp` setting with the
numbers, both ways*. `altitude` carries output-determined specs, the operand
selection rule, `Triple` not framing the state, and named refusals. `frame`
carries the `PstAt` shape and re-founding-proof vs inlined. `fold` carries
never-both-directions and the flat `∧`-chain.

**The placeholder is an unknown tactic on purpose.** `sorry` is forbidden
outright, and *a scaffold that elaborates is a scaffold that can be committed
unfinished* — `proof_goes_here` fails loudly, which is the failure direction
this repo asks for everywhere else.

### `analogues.sh <shape>` — the Lean lane's tractability estimate, as a tool

The M2 census picked its first proof target on evidence about the
**neighbourhood**, not the subject: *"26 proved analogues around it at a
median of 15 lines"* (`2026-08-22-lean-tier-2`). A shape with 26 neighbours at
15 lines is routine work; the same shape with 2 at 200 lines is a research
project wearing a theorem's clothes. Twelve named shapes — the cookbook's
entries, so a lane that read one can measure it without inventing a regex —
plus any ERE. Live: `frame` → **7 analogues, median 8, range 4..23**, the
shortest being `PstAt.push` itself; `triple` → **12, median 5.5**.

It reports **what tree and sha it was measured at** (MEAS-10), and a zero
result is stated as *a finding about the shape or the regex, not evidence
that the proof is hard* — §5.4's empty-census law pointed at a grep.

### Both self-tests caught a real defect in their own instrument

`new-proof.sh --self-test`: **31 ok, 0 failed** — but its first version failed
three templates for containing a law **twice**, because the helper used
`grep -c` (a *line* count) where it meant presence. `analogues.sh
--self-test`: **16 ok, 0 failed** — its first version predicted a median of
2.5 and measured **3.5**, because block length ran to the next construct and
so **added the trailing blank line to every entry**: a constant bias on every
number the tool would ever report. Both are fixed; both were found by a test
that predicted a number rather than admiring an output. Double-run
byte-identical is asserted on the scanner itself (§5.4).

**No Lean was executed by any of this.**

---

## 2026-08-22-qol-9 — AMENDMENT 16: the 3 GB chain cap was killing honest builds, and the guard was in its own kill set

Audit #2 measured **one honest `lean` worker at 3251 MB** against A11's single
**3 GB line over the whole chain**. A chain cap below the size of a single
legitimate worker is not a resource guard, it is a coin flip — and it is
expensive twice, because the kill lands mid-build and the log reads as a
resource kill rather than as a policy error.

Three defects, one amendment, all three now implemented in `tools/triad.sh`:

1. **PER-PROCESS, 5 GB**, chain kept as a secondary at **10 GB**. The
   per-process line kills *the offending process*, not the chain.
2. **THE GUARD EXCLUDES ITSELF.** The old kill set was `descendants $$`, which
   **contains the watchdog**; the guard reaped itself along with the chain.
3. **RESTARTED PER ATTEMPT.** Because the guard died with its own kill, base
   rule 2's retry ran **attempt 2 completely unguarded** — the attempt most
   likely to need one, since attempt 1 had just exhausted the machine.

The decision is now a **pure function** (`rss_verdict`: rows in, verdict out)
for one reason: the old guard's logic lived inside a background subshell where
it could not be exercised, and it was wrong in three ways at once. What cannot
be run cannot be checked, and this is what that costs.

### The regression is a test row, not a note

`printf '4242 3329024' | rss_verdict` — the measured 3251 MB worker — returns
**`ok`** under A16 and **`proc`** under the old 3 GB numbers. Both directions
are asserted, so the amendment cannot be silently reverted by a future edit.

### The banner, and why /tmp copies exist at all

Audit #2 found **two drifted copies in `/tmp`**. Copying before editing is
*legitimate*: bash reads a script **incrementally**, so editing one that is
running corrupts it. But a copy whose diffs never land is a private script
again, at the 38% violation density §7.1a already prices. Every run now prints
`tools/triad.sh — protocol base 1-6 + A4-A13 + A16 (2026-08-22), <sha>`, and
`--version` prints it alone. Drift becomes visible in the log.

### The model landed first, from the other side, and that is the good case

This lane wrote the register row and the paragraph — and hit a **conflict**:
the calmness lane had already landed **rows 14, 15 and 16** with a fuller A16
than mine, naming the same two implementation defects (self-exclusion, restart
per attempt) plus a **16.2** on retiring a runner that I did not have. So my
paragraph was **dropped, not merged**: theirs says it better and says more,
and a second copy of one amendment is the defect
`docs/duplication-audit.md` measured. What I kept is the one thing theirs
lacks — the **protocol banner** — as a short paragraph in the same section.

Model and code still land together; they arrived from opposite directions,
one tenure apart. **The doc specifies A16 and this script now implements it**,
which is the only sense in which "together" is checkable.

### One thing this lane got wrong, recorded

While verifying the banner I ran `--dry-run`, which **takes a real tenure** —
the header says so plainly. It queued behind the `ada` lane's live lock and
had to be killed. **A no-Lean lane has no business in the ticket queue**, and
the release trap did exactly its job on the way out: my ticket was removed,
and A7 left the `ada` lane's lock alone because it was not mine. The refusal
paths held; the operator did not.

### Triad

`bash -n` clean. `--self-test`: **78 ok, 0 failed** (61 → 78, **17 new**) —
the 3251 MB regression in both directions, the per-process line and its
boundary, the chain line firing at four workers and not at three,
per-process outranking chain, an excluded pid never being the victim and never
counting toward the chain while its siblings still are, guard restart
replacing the old pid, the pidfile the exclusion reads, stop clearing it, and
the banner naming the protocol level. **No Lean was executed.**

---

## 2026-08-22-qol-10 — the GATE PHASE was building the tree, and it defeated every narrowing

Found by the R-track running a narrowed build. `harness/diff_test.py` runs an
**unconditional `lake build`** before its cases (line 355), and every
runner-driven gate — `diff_test`, `script_corpus`, a lane's `monadic_gate` —
invokes `lake exe leanmodels-run`, **which builds**. So a narrowed tenure got
a full build anyway, *inside the gate phase*, where it is accounted as a gate.

Two costs, and the second is the one that matters:

1. the build/gate accounting is misleading — the tenure reports a scoped build
   and then quietly builds the tree;
2. **an unrelated build failure surfaces as a GATE failure**, which makes the
   coverage statement false **in the flattering direction** (§5.4a). A run
   that says *"scoped: covers these modules"* while having built the whole
   tree is claiming **less than it did**, and a tree failure it caused is
   filed against a gate that was innocent.

### The fix: pay for it where it is accounted

A narrowed tenure now builds what the gates need **explicitly, before
invoking them**, and names it:

```
[HH:MM:SS] === gate-phase build: leanmodels-run (the gates invoke it; built HERE, not inside a gate) ===
[HH:MM:SS] gate-phase build done; LS_RUNNER_PREBUILT=1 and diff_test gets --no-build
[HH:MM:SS] COVERAGE (§5.4a): gate phase additionally built: leanmodels-run
```

If that build fails it is reported as a **BUILD failure and the run stops** —
letting it reach the gates is precisely the misattribution the block exists to
stop. The exe names are **read from `lakefile.toml`**, and `diff_test` and
`script_corpus` are recognised as runner-drivers even though the runner's name
never appears in their gate string, because it is their **default**.

Then the gates are told the runner is ready: **`--no-build`** for `diff_test`
— its own documented flag, added idempotently — and **`LS_RUNNER_PREBUILT=1`**
in the environment for every other harness. No flag is invented for a harness
that does not have one; that would turn a build defect into a gate crash.

Only a **narrowed** tenure does this. After a full build the runner is already
current and the gates' own `lake build` is a no-op that cannot fail.

### One part of the dispatch is NOT actionable here, and that is the finding

`harness/monadic_gate.py` **is not on master**. It exists only in commit
`6a15cf2` on a feature branch; `git grep` over the working tree finds nothing.
So its unconditional `lake build` at line 146 **cannot be fixed from here** —
I will not edit a file that is not in the tree, and I will not report a
one-line change I did not make.

**OWED TO THE R-TRACK, as a contract rather than a diff:** when
`monadic_gate.py` lands, it must (a) drop the unconditional `lake build`, and
(b) honour **`LS_RUNNER_PREBUILT=1`** by skipping any build of its own — the
same shape `diff_test --no-build` already has. `triad.sh` exports it today, so
the harness side is the only missing half.

### Triad

`bash -n` clean. `--self-test`: **88 ok, 0 failed** (78 → 88, **10 new**) — exe
names read from the lakefile, the tier floor needing the runner and the docs
floor not, `script_corpus` recognised by its default, a named exe taken
literally, the `--no-build` rewrite exact, said **once**, **idempotent**, and a
non-`diff_test` gate left untouched. That last group is property (4) stated as
a mechanism: `--no-build` is *how* a narrowed run's log carries no full-build
lines from the gate phase. **No Lean was executed** — this lane holds no
ticket, so the gate-phase build itself is exercised by its decision functions,
not by running it.

---

## 2026-08-22-qol-11 — §9.5 FINISHED: the monolith is frozen, the index is generated, and the id drifter is dated

§9.5 was landed as a scheme and left half-adopted: the monolith took **10 more
commits after v2** and stands at **21,797 lines**, and the "generated index"
it promised did not exist. Three moves close it.

### 1. The monolith is frozen, and 111 citations still resolve

`docs/backlog.md` → **`docs/backlog-archive.md`**, with a header that says
FROZEN, points at `docs/backlog/<lane>.md`, and states that **every `§Lnn`
reference still resolves at the heading it always had** — nothing is
rewritten.

**And `docs/backlog.md` stays, as a twelve-line redirect.** Measured before
deciding: **111 tracked files cite that path**, including `.lean` files —
whose edit would make a docs landing **tier-class** and demand a tenure this
lane does not hold. A big-bang sweep is what §9.2 forbids in as many words, so
the old spelling retires **by touch**, and until then a citation that lands
here is one hop from its target. The stub says FROZEN too, so a lane that
opens the old path is told where its entries go.

### 2. `tools/backlog-index.sh` — the index §9.5 promised

`docs/backlog/INDEX.md`, **36 entries across 12 lanes**, newest first, one row
of id + title + lane. Generated, never hand-maintained (§5.5).

The trap it was written around: **a lexicographic sort puts `-10` before
`-2`**. Ids sort by date and then by the entry number **as a number**, and
that is a self-test row rather than a hope. An **undated heading is reported,
not dropped** — a drifter quietly skipped is a row nobody sees is missing — so
it gets a line and the page says how many there are.

Wired as a **notice, not a gate**: `tools/docs_check.py` reports a stale or
missing index in every triad, and `tools/backlog-index.sh --check` is the
gate for anyone who wants the exit code. A hard gate would red every lane that
appends an entry without regenerating, and springing that on lanes mid-tenure
is a coordination cost to schedule rather than to impose. Both directions are
verified: stale → the NOTE fires; regenerated → silent; `--check` → `in sync
(36 entries)`.

### 3. The one id drifter is dated

`docs/backlog/go.md`'s `## G1` → **`## 2026-08-22-go-1`**, carrying
`(formerly §G1)` so any citation resolves, and the file's header now states
the §9.5 scheme like every other lane's. Nothing cited `§G1` yet — checked,
not assumed.

### Triad

`bash -n` clean. `backlog-index.sh --self-test`: **15 ok, 0 failed** — rows
from headings, lane from the filename, title from the em-dash tail, newest
first with **10 outranking 2 numerically**, a drifter flagged and sorted last,
`INDEX.md` excluded from its own input, **double-run byte-identical** (§5.4),
and `--check` verified in **both** directions (MEAS-42). `docs_check`
**83/83**. Docs-and-tools landing: no build, **no tenure**, no Lean executed.

---

## 2026-08-22-qol-12 — `--foreign`: the tenure is about THE MACHINE, the gates are about the tree

The Lean tier works in `lean4lean`; the Wasm lane works in a `spectec` fork.
Both need the tenure — **the lock, the ticket and the RSS discipline are
properties of the machine, not of the repository** — and neither can use
anything else this script assumes.

§7.1a already states the hazard: **`--classify` is our-repo-only by
construction**, and a lane pointing it at a foreign checkout gets *a confident
wrong answer rather than an error*, because the class floor hard-wires
`docs_check`/`diff_test` and classification diffs against `github/master` —
which, in a foreign clone, is **upstream's** master. So `--foreign` takes the
full tenure, runs **only the lane's `--gates`**, skips classification
entirely, and states what its green covers:

```
COVERAGE (§5.4a): foreign checkout <remote>; gates as given; class floor not
applicable — this green is evidence about THAT tree and those gates, and about
nothing in this repository.
```

### Two refusals, stated before a ticket is ever written

* **`--foreign` without `--gates` REFUSES.** The floor does not apply, so
  there would be *nothing to run* — and naming a gate that does not exist
  there is exactly the failure the refusal prevents.
* **`--foreign` with `--classify` is an error**, with the contradiction
  spelled out rather than silently resolved in someone's favour.

Both fire in the precondition phase, so a contradictory invocation never
reaches the queue. The banner marks the run `[FOREIGN]`, so a foreign tenure
is identifiable in a log at a glance.

Two facts this builds on, both verified rather than assumed: **`--dir` already
relocates the build correctly**, and **elan resolves the toolchain per
directory** — so a foreign checkout's own pin is honoured without this script
doing anything about it.

### Triad

`bash -n` clean. `--self-test`: **98 ok, 0 failed** (88 → 98, **10 new**).
Both refusals are exercised **by invoking the script itself** and asserting
exit 2 plus the message; the accepted path runs end to end under a
**sandboxed lock and queue** with `--dry-run`, proving it reaches the tenure,
prints `[FOREIGN]`, and **leaves no ticket behind**. The gate phase is
unreachable without Lean, so what is asserted there is the decision — the
coverage statement names the remote, says the floor is not applicable, and
**claims nothing about this repository**. No real lock was taken and **no Lean
was executed**.

### Correction, same day: the count above was PREDICTED, not measured

The entry and the commit message for this landing first said **99 ok (11
new)**. The measured number is **98 ok (10 new)** — I counted the checks I
intended to write rather than reading the ones the run reported. It is a
harmless number attached to a green run, which is exactly why it is worth
recording: **§5.4a is not a rule about important numbers**, it is a rule about
where every number comes from, and a figure written from intent rather than
from output is the failure mode in its cheapest form. The commit message
carrying `99` is already on master and is **not rewritten** — shared history
does not get rebased to hide an error; it gets a correction that points at it.

---

## 2026-08-23-qol-13 — `--gates` ADDS; unstaged Lean under a glob REFUSES; Lean nothing imports is LOUD

Three fixes, all from one 78-minute Ada tenure.

### 1. `--gates` adds, `--gates-only` replaces

Without `--classify`, `--gates` **silently replaced** the default set:
`--gates "docs_check"` dropped the differential and the run went green against
fewer checks than the default it thought it was extending. That is the **exact
mirror** of the narrower-default trap the ES lane found (`qol-6`) — a gate set
that shrinks without saying so — and the two now have one answer:

* **`--gates` ADDS to the floor** (the class floor under `--classify`, the
  default floor without it). This script cannot tell "also run mine" from
  "instead of yours", so it takes the reading that **cannot silently shrink a
  gate set**.
* **`--gates-only` REPLACES**, and announces which floor gates it is skipping.
  Replacement is now a flag you have to type.
* **`--foreign` implies `--gates-only`**, because there is no applicable floor
  in a foreign checkout.

### 2. Unstaged Lean under a lake glob is a REFUSAL

A tenure verifies the **staged** tree. Spending one on a tree whose Lean is
not staged verifies something nobody is landing — those files get compiled but
not landed, or landed but not compiled. The check counts **untracked** files
too, because Ada's `Value.lean` was untracked rather than merely unstaged.
Live: exit **2** with the files named. Under `--classify-only` it is reported
and **not** refused — no tenure is at stake there, so a refusal would be
theatre.

### 3. Lean that nothing imports gets a loud line

`Value.lean` was untracked **and unimported**. The `LeanModels` library
declares **no `globs`** in `lakefile.toml`, so lake builds `LeanModels.lean`
and its transitive imports **only**: a new module nobody imports is never
compiled, and a green build is **green about nothing** where it is concerned.

It is loud but **not** a refusal — the file may be landing together with the
import that will reach it. Two exemptions, both read from the lakefile rather
than assumed: **`LeanModels.lean` itself** (the library root, imported by
nothing by design), and **everything under `Examples/`**, which declares
`globs = ["Examples.+"]` and is therefore a target whether or not anything
imports it.

### The collision that did not happen

This landing rebased onto the rebuild lane's `--build-target`, which arrived
while this work was in flight. **They compose**: their flag unions into
`BUILD_TARGETS` through the same `add_build_target` the classifier uses, and
their own self-test asserts "UNION with the classifier's floor, never
replacement". Nothing had to be reconciled — the union was designed for this
in `qol-1`, and it held.

### Triad

`bash -n` clean. `--self-test`: **118 ok, 0 failed** (102 → 118, **16 new**;
102 already included the rebuild lane's four). Gate composition in all four
combinations plus the announcement; lake-glob detection distinguishing a doc's
`.lean` and a non-`.lean` path; import detection against a real fixture tree,
with the orphan reported, the imported one silent, and both exemptions
asserted. Live on this tree: the refusal exits **2**, `--classify-only` exits
**0** and reports, and the unimported line fires on a staged orphan. **No Lean
was executed.**

### The count was wrong AGAIN, and twice is a process defect

`qol-12` reported a predicted 99 against a measured 98, and was corrected.
This entry then did the identical thing: **119 written, 118 measured**. One
slip is a slip; the same slip twice in three landings is a **process defect**,
and the process was "write the entry, then run the self-test, then don't
re-read the number."

**The fix is ordering, not care.** The measured line is now pasted from the
run into the entry — the self-test is run *first*, its last line copied, and
the entry written around it. A number that is typed from intent has no
provenance at all, which is §5.4a's subject exactly: *a number carries the
state it was measured in.* Both wrong figures were attached to green runs, in
entries whose whole purpose is to be citable later — which is what makes the
cheap version of this failure worth two corrections rather than one shrug.

Neither commit message is rewritten. `4d32526` and `92fcfcb` carry the wrong
figures on master, and this line is how they resolve.

---

## 2026-08-23-qol-14 — the INDEX collision is mechanical now: a merge driver, and a refusal before the ticket

§9.5 moved the backlog's rebase collision off the §-numbers — where `L2`, `L3`
and `L4` each appeared twice — and onto one generated file. The ES lane hit
it: two lanes appending on the same day both regenerate `INDEX.md`, and the
diffs overlap. **Merging a generated file is always wrong**; the merged result
is a *third* version matching neither tree. The correct resolution is take
either side and regenerate, and that is now mechanical.

### `.gitattributes`, and the half that is easy to ship broken

`docs/backlog/INDEX.md merge=ours` — so a rebase resolves without a conflict,
leaving the index **stale-but-valid** until regenerated.

**But the attribute alone does nothing.** `ours` is **not** one of git's
built-in merge drivers — those are `text`, `binary` and `union` — so each
clone must also define `merge.ours.driver`. Measured both ways before
shipping: without the config the same merge **still conflicts** (markers in
the file); with it, it resolves to our side. Both directions are self-test
rows, so the day someone deletes the config line the test says which half
broke. `tools/backlog-index.sh --install-merge-driver` sets it, and the header
of the generated page now opens with **"CONFLICT? REGENERATE with
`tools/backlog-index.sh` — never merge."**

### One correction to the dispatch: the docs_check rule did NOT exist

The brief said a docs_check rule refusing a stale index "already exists". It
does not — `qol-11` shipped a **NOTE**, deliberately non-fatal, and said so.
That gap matters more now, because `merge=ours` makes a stale index the
**routine** post-rebase state: a driver that resolves quietly plus a check
that only whispers is a mechanism for landing stale artifacts.

So the refusal now exists — **in `tools/triad.sh`'s preconditions, not at the
docs_check gate**, and the placement is the point. Base rule 4 makes a triad
**one per landing**, so a red at gate 2 costs the whole tenure; a refusal
before the ticket costs **one command**. Same refusal, one tenure cheaper —
and this lane has watched a tenure cost 78 minutes. It is scoped to landings
that **touch `docs/backlog/`**: another lane's stale index is not this lane's
refusal to eat. Under `--classify-only` it reports and does not refuse, since
no tenure is at stake. The `docs_check` notice stays for runs outside the
triad, and `--check` remains the standalone gate: three layers, each at its
own cost.

### The installer shipped a bug that the self-tests did not cover

`--install-merge-driver` worked and printed `ours: command not found` — a
backtick inside a double-quoted `echo`, so the shell ran `ours` as a command.
The config was set correctly, so **every behavioural test passed**; what was
broken was the part only a human reads. There is now a check that the
installer's output contains **no shell error text**, which is the same lesson
this repo keeps paying for in different costumes: a test that asserts the
effect and never reads the output is a test with a blind spot exactly the
width of the message.

### Triad

`bash -n` clean. `tools/triad.sh --self-test`: **122 ok, 0 failed** (118 →
122, **4 new**: a freshly generated index is not stale, an un-regenerated one
is, regenerating clears it, and no generator means nothing to be stale about).
`tools/backlog-index.sh --self-test`: **25 ok, 0 failed** (15 → 25, **10
new**: the shipped attribute resolving to `ours` on `INDEX.md` and
`unspecified` on an ordinary doc, the merge conflicting **without** the config
and succeeding **with** it, our side kept, no third version, the config set,
the installer's success line, its silence on shell errors, and the header's
conflict instruction). `docs_check` **83/83**. Live: the refusal exits **2**
naming the file, and a regenerated index passes. Tools-only: **no tenure, no
Lean executed.**

---

## 2026-08-23-qol-15 — `check.sh --iterate`: a COURTESY PROTOCOL whose only guarantee is the RSS ceiling

The C lane measured **~85 minutes per compile** for a 300-line proof under
"one tenure per compile". That is not a slow loop; **it is no loop at all**.
`--iterate` runs a single-shot `lake env lean` on a **library** file — the case
§7.1 rule 3 does not cover — **without a ticket**.

Implemented to **A17's five tightenings**, which supersede the first dispatch
where they differ.

### It is framed as a courtesy protocol, and that framing is the honest part

Everything this mode does to stay polite — the load line, the swap line, the
single slot, yielding to the owner's workloads — is **checked at the moment it
starts and enforced by nothing afterwards**. Another lane can take a tenure a
second later and nothing stops this process. So `--help` says it plainly:
**the only guarantee is the RSS ceiling**, 3 GB on its own chain, and it
**kills rather than pauses**, because nothing else is watching an unticketed
process. That ceiling is deliberately **stricter than A16's 5 GB per-process
tenure line**: a tenure has a watchdog and a lock behind it; an iterate has
only this.

### The five tightenings

1. **The slot is MACHINE-WIDE**, not per-lane — a shared `/tmp/ls-iterate/`
   with one live entry total, staleness by the two-part test. Two lanes
   iterating is the shape that took the box down at load 29, only smaller.
2. **An explicit RSS kill line at 3 GB** on the iterate's own chain — and,
   applying A16's lesson at this scale, **the guard is not in its own kill
   set**.
3. **The STOP mirrors the START on both axes.** One function decides both, so
   the mirror is true *by construction* rather than by two lists agreeing: a
   loop whose machine degrades mid-flight is refused its **next** run, by
   number. Load and swap never kill a run in progress; only the ceiling does.
4. **The provenance line names the priority clause** — *"yields to owner
   workloads (Thomas's own processes have absolute priority, A11)"*.
5. **The whole mode is framed as courtesy in `--help`.**

Every run prints what it was permitted by, so a green carries its own
provenance (§5.4a) rather than resting on a claim that the machine *was*
quiet.

### The citation checks itself, and "present" is not "adopted"

A17 had **no row** in §7.1a when this was written, so the tool grepped the
register at run time and said so. **While the work was in flight the row
landed — marked `DRAFT`** — which would have silently switched the honest note
off. So the check now distinguishes **three** states: absent, **draft**, and
adopted, and only the third is silent. Today it prints *"A17 is in §7.1a but
marked DRAFT. Present is not adopted."*

The register row is the arch lane's to promote; this lane does not edit
another lane's amendment text. **The note clears itself when the row does.**

### Every reader is mockable, because a guard nobody can trigger is untested

`read_load`, `read_swap_pct` and `has_lean_descendant` honour mock variables,
so the self-test drives **each refusal**. The machine-wide test uses a **real
foreign pid** from a different lane name — a live `sleep` — rather than a
simulated one.

### Live, on the machine as it actually was

The box sat at **load 19–33 and swap ~90%** throughout, so every live run
**refused by number**. That is the demonstration that matters: the happy path
is exercised through `--explain` and its decision functions, never by running
Lean, because this lane holds no ticket and the machine was never quiet enough
for its own tool to permit it.

### Triad

`bash -n` clean. `tools/check.sh --self-test`: **58 ok, 0 failed** (26 → 58,
**32 new**) — the courtesy framing and the priority clause in the WHY, the
same file refused by the ticket path and permitted by the iterate path,
stop-mirrors-start asserted on **both** axes and shown to be the same function
the refusal quotes, load exactly at the line allowed, a cold clone naming A13,
**a second iterate refused across lane names** with the stale entry reaped,
all four staleness states, our own entry never blocking us, the RSS ceiling in
**both** directions plus the offender it names, and the A17 citation in all
three states. `triad.sh` **122 ok**, `backlog-index.sh` **25 ok**, `docs_check`
**83/83**. **No Lean was executed.**

---

## 2026-08-23-qol-16 — the triad summary now says what it knows: counts from the full log, and an aborted triad called one

Measured on the wrapper itself (§7, master `9ade44d`): the "first failures"
block was `grep -E '^error|✖' | sort -u | head -8`, and **a lane reported "one
error in 839 targets" off it — a number that then travelled up the chain.**

Three things were wrong at once, and only the third is obvious: the preview is
**deduplicated**, it is **truncated at eight**, and **`lake` stops at the first
failing module**, so the log being summarised is already partial. A count
taken from that block is a **lower bound on sites, never a count.**

### What the wrapper prints now, on any red build

```
[06:54:14] BUILD DID NOT COMPLETE (exit 1)
    failed modules   1   (✖ lines)
    error lines      12 total, 12 distinct
    targets          502 of 839 when lake stopped — and lake stops at the FIRST failing module
    first 8 of 13 (summary LOCATES; the full log COUNTS):
      ...
    These counts say how far the build GOT, not how much of the tree is broken.
[06:54:14] GATES NOT RUN (build red — aborted triad)
```

**The amplification gap is named**, because it is exactly what turns one root
cause into a frightening number — or a comforting one. Forty identical error
lines from one bad identifier now read `40 total, 1 distinct — AMPLIFIED
40.0x`, and the deduped pool is reported as `first 2 of 2` rather than
silently standing in for forty.

**And `GATES NOT RUN (build red — aborted triad)`** is printed as its own
line. A red build short-circuits the tenure, so a red triad yields a
build-error list **and nothing else** — no `docs_check`, no `diff_test`. It is
not a triad result with one part failing; **reporting it as "triad: 1 failure"
claims two gates that never executed.** Both red paths get the block: the main
build and the gate-phase build.

Also removed: the two dead `*monadic_gate*` patterns. That harness was
**deleted on master in `eeeb1fd`**, which closes `qol-10`'s open item — it was
recorded there as *owed to the R-track*, and the resolution turned out to be
deletion rather than a fix.

### Doc-first, and the doc had gone stale in one word

§7's law landed ahead of the code, which is the right order. But its diagnosis
quotes the old block in the **present tense**, and the code has just made that
false — so §7 now carries a short `IMPLEMENTED` note marking the quoted block
as *the defect as found*. Model and code agree again; the incident record is
untouched.

### Triad

`bash -n` clean. `--self-test`: **142 ok, 0 failed** (122 → 142, **20 new**).
The summary is the instrument that reports the other instruments, so it is
tested against two synthetic logs: one with **12 distinct errors and 3 failed
modules** (asserting the counts, `502 of 839`, the `first 8 of 15` label, that
the preview really is eight lines, and that **no** amplification is claimed
when there is none), and one with **40 lines from a single root cause**
(asserting `40 total, 1 distinct`, the named `40.0x`, and the deduped pool).
Plus a log with no progress lines (`targets unknown`), a missing log refusing
honestly, the `GATES NOT RUN` line with its headline and counts intact, and
the deleted harness no longer matched while the live ones still are.
`docs_check` **87/87**. Spine edit, no Lean executed — the self-tests drive
synthetic logs, so no tenure was needed.

---

## 2026-08-23-qol-17 — `tools/sites.sh`: price a constructor change by what DESTRUCTURES it

Three lanes priced one constructor change three different wrong ways in a
week — importers **2**, transitive reachers **128**, a name grep **over by 4**
— and §5.4a records the calibration: the right unit is **the sites that
destructure it**, and the law is *name the TYPE first, then grep its
constructor's pattern, wherever that type rides.*

`tools/sites.sh <Type> <ctor>` implements it and reports three buckets:
**CONSTRUCT**, **DESTRUCTURE** (match arms plus the `#guard`/`rfl` pins that
fix the shape), and **LOOK-ALIKES excluded with the reason** — because an
exclusion nobody can audit is just a smaller wrong number.

### Live on this tree, and the numbers are the argument

**21 types declare a constructor named `unsupported`.** The tool excludes
**1250** hits — **1207 by position** (no channel this type rides) and **43 by
prefix** (`.unsupportedDevice`, `.unsupportedConstruct`, six more) — to report
**9 destructure + 15 construct**. A bare name grep would have returned about
**1274**. The convicting case from the doc is found: `Examples/go/rung1/`
`guards.lean`'s `refusalOf`, which destructures `.error (.unsupported _ m _)`
and **names no Core symbol at all** — invisible to an importer count, which is
why that count was never a bound.

The doc cites it as `guards.lean:80`; it is at **line 88** today. The tool
asserts the **file and the symbol**, never the line — a line number is exactly
the kind of number that goes stale between the measurement and the citation.

### Calibrated against the three recorded cases

Fixtures reproduce each shape and assert the doc's decomposition: **ES 5
destructure + 2 construct = the honest 7, with 3 look-alikes**; **C 8 construct
+ 8 destructure through the `Halt` channel**, where `.error (.unsupported`
returns **zero** — the under-count that reads as *"no work to do"*; and the Go
case above.

One number is deliberately **not** asserted. The doc records ES's raw grep as
**8**, but not the pattern that produced it, and 5 + 3 = 8 only under a reading
I cannot verify. The test asserts the decomposition the doc **does** record,
plus the law's own point — *no single grep produces the number* — rather than a
figure whose provenance cannot be reconstructed. Same for the dispatch's C
figures: it said **2+6 / 5+3**, the doc says **8 construct + 8 destructure**,
and the sums agree, but no sub-split is recorded anywhere, so the totals are
what the calibration uses.

### Three defects in my own instrument, all found by testing it

1. **A phantom exclusion per empty file.** Files with no hits sent one empty
   line through the loop and were filed as look-alikes — **~300 phantom
   exclusions** on the real tree. §5.4's law, biting the tool written to serve
   it: a zero-row read is an instrument fault, not a finding.
2. **Match arms counted as declarations.** The declaration scanner attributed
   `| unsupported` inside a later `def` to the last `inductive` seen, so the
   live run reported `Run` five times and `Hands` three. That is the
   identifier law failing *inside the tool that exists to prevent it*; leaving
   the inductive block now ends the run, and 27 became 21.
3. **`awk -v` eats one backslash level**, so `\.` became a **wildcard** dot and
   matched the space in `| unsupported (m : String)` — a declaration counted
   as a use. There is now a regression row asserting the dot is literal.

And a fourth found by reading the first live output: **comments are not
sites**. Six doc-comment mentions of `Halt.unsupported` were counted as
CONSTRUCT sites, including a markdown table inside `Core/Outcome.lean`. The
scanner now strips Lean comments — nesting `/- -/` correctly — before looking
for the token, which `harness/wasm_sorry_census.py` already had to learn
(`docs/backlog/wasm.md 2026-08-22-wasm-1`). That alone moved CONSTRUCT from 21
to 15.

### Docs-first

§7 had **no tools list at all**, so one landed with this: ten tools, one line
each, naming the law each implements. Unnumbered, to avoid colliding with a
§7.x another lane may be drafting.

### Triad

`bash -n` clean. `--self-test`: **25 ok, 0 failed** — the three calibration
cases, the classifier on the four real shapes it must tell apart (an arm, a
right-hand side, a line that does **both**, and a `#guard`), comment stripping
including a nested block, the literal-dot regression, and the no-hits-no-
phantom rule. `docs_check` **87/87**. No Lean executed; no tenure needed.
