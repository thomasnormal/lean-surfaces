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

---

## 2026-08-23-qol-18 — the tree must not move while you queue, and now it cannot silently

A queued tenure reads the source at **build** time, not at enqueue time. So an
edit made while waiting **silently changes what the verdict is about** — and
measured this morning, the Lean tier nearly reported **"instN green"** for a
run that would have built **instN + weak'**. The queue wait outlasted the
tree.

`tools/triad.sh` now stamps the index's tree (`git write-tree`) plus `HEAD`
**into the ticket** at enqueue — so a human reading the queue can see what each
waiting lane is waiting *for* — re-takes the stamp at acquire, and on a
difference prints:

```
TREE CHANGED SINCE ENQUEUE (6a8b1bd6f8d9 → 91c4e0a72b15)
```

and **refuses**. `--build-current-tree` proceeds for a lane that batched an
edit deliberately, and prints **the same line** — because the run is about a
different tree either way, and the only thing the override changes is who
decided.

### Three directions, and the third is the one that keeps it usable

* **changed → refuse**, naming both trees and saying to re-enqueue;
* **unchanged → proceed silently** (a gate that narrates its successes is a
  gate people stop reading);
* **unstampable → proceed, LOUDLY.** A non-git directory or an unreadable
  index cannot prove the tree held, and refusing there would block `--foreign`
  and every non-repo use for a fact nobody can establish. It prints `TREE STAMP
  UNAVAILABLE — this run cannot verify the tree is the one it queued for` and
  continues. Saying *"I could not check"* is not the same as saying *"it is
  fine"*, and the line exists so the two never read alike.

### Doc-first, and the division of labour

§7.2 now carries the enforcement paragraph next to A6's torn-tree rule. The
**amendment text is the arch lane's** — A6 is being extended to *"never change
the tree between enqueue and release"* — and this lane wrote the gate, not the
rule. That split is the point: **fixes live in gates**, and a rule whose only
enforcement is prose is a rule that gets guessed. The doc says so and points
here.

### Triad

`bash -n` clean. `--self-test`: **156 ok, 0 failed** (142 → 156, **14 new**) —
the verdict on identical stamps, a moved tree, a moved **HEAD**, and an
unstampable side; then a **real git repository** stamped, edited and re-stamped
so `git write-tree` itself is exercised rather than mocked; then all three
report directions including the shared line, that a clean pass prints
**nothing**, and that the unstampable case is loud. Live: a sandboxed dry-run
enqueued, printed `tree at enqueue: 6a8b1bd6f8d9`, acquired and proceeded with
no complaint, leaving no ticket. `docs_check` **87/87**. No Lean executed.

---

## 2026-08-23-qol-19 — a run is not a measurement until it has been read

The successor lane's instrumented proof run counted **"0 open arms" twice**
while it was (a) looping in `simp` until the heartbeat timeout and (b)
erroring inside a `first` chain — `split` fails **hard**, escapes the chain,
and never reaches the fallback the counter counts.

> **A counter that counts goals reaching a fallback reads an ERROR as a
> SUCCESS.**

That is `#print axioms` on a failed statement wearing different clothes: **a
success signal that survives the failure it should report.** Same family as
`diagnose.sh:axioms-clean-lie`, and the same fix — read the state, don't infer
it from the absence of a complaint.

### What `check.sh` now prints after every run

```
    exit code      1
    warnings       2 total — 1 sorry, 1 other
      other: unused variable 'fuel'
    heartbeats     1 line(s) — THE RUN DID NOT FINISH THINKING:
      f.lean:1:1: error: (deterministic) timeout at `whnf`, maximum number of ...
    maxRecDepth    none
  VERDICT  NOT A MEASUREMENT: exit 1; 1 error line(s); heartbeat timeout; 1 non-sorry warning(s): unused variable 'fuel'
```

versus `VERDICT  TRUSTWORTHY: exit 0, sorry-only warnings`.

Four decisions worth naming:

* **Both runaway modes print even when they did NOT fire** (`heartbeats
  none`). An absent line is information; it is what lets a lane trust the run
  without re-reading the log.
* **An error line voids the verdict even at exit 0** — that is the escaping-
  `first`-chain case exactly, and it is a self-test row.
* **A non-sorry warning voids it too**, and its class is listed. §L88 already
  records an unused-variable warning that *was* a fidelity bug: unused fuel
  meant the walk was not happening.
* **`--axioms` runs a temp copy with `#print axioms` appended**, so the axiom
  lines come from the **same elaboration** whose exit code is being read — an
  axiom print from a different run is a number without its state. And they are
  reported **only** when the run was a measurement; otherwise the section
  refuses by name and cites §0.1 II(a).

### The fixtures were wrong before the code was

My first synthetic outputs used `warning: file:line: text`. Lean's real shape
is `file:line:col: warning: text`, and the class extractor — which strips
everything up to `warning:` — returned the file path instead of the message.
The test failed, and it was the **fixture** that was wrong, not the tool. A
synthetic output that does not match the real one tests a program nobody runs.

### Triad

`bash -n` clean. `tools/check.sh --self-test`: **74 ok, 0 failed** (58 → 74,
**16 new**) — a clean run, a sorry-only run, a nonzero exit, an **error at exit
0**, a heartbeat timeout called out and named in the verdict, `maxRecDepth`
called out and pointing at its three causes, a non-sorry warning voiding the
run with its class listed, no output at all, and the axiom section refusing on
a failed run while reporting on a clean one. Docs-first: §7's tools list gains
the verdict row and the law. `docs_check` **87/87**. **No Lean executed** — the
verdict is a function of `(exit code, output)`, so it is tested on synthetic
outputs, which is also the only way to test the failing cases at all.

---

## 2026-08-23-qol-20 — `tools/laws.sh`: which laws have a gate, and which are only prose

§9.7's cadence had been walking the laws **by hand**, which is the shape §5.4
exists to retire. The rule it serves is blunt — **fixes live in gates**, and a
law whose only enforcement is prose was measured at a **38% violation
density**, by lanes that had read the protocol.

`tools/laws.sh` reads `docs/law-index.md`, §7.1a's amendment register and §7's
tools list, and reports per law the tool that cites its durable home — or
**`NO GATE`** — then sorts that list by **how many lane ledgers cite the law**,
so the next inch is chosen by **measured demand** rather than by whoever
remembers a rule at the time.

### First run: 332 laws, 206 cited, **126 with no gate**

Two honesty clauses, and they are what make the number usable:

* **Citation over-credits.** This greps text; it cannot tell a gate from a
  comment, and a tool that merely *mentions* §7.1a is counted. So the NO GATE
  list is a **LOWER BOUND on the unenforced set — never a coverage figure.**
  Same shape as §5.4a's destructure count: a bound you can act on, not a
  census you can report.
* **The unit the count ranks is the HOME, not the law.** Laws sharing a `§`
  share every token and therefore tie. That is information, not noise — it
  says the *section* is what the ledgers keep reaching for — so the report
  prints both views, and the grouped one is the actionable one.

### The top five NO GATE laws, by ledger citations

| cites | id | law | home |
| ---: | --- | --- | --- |
| 24 | `STMT-67` | a second semantics owes an adequacy theorem | §8.5 (with §3.4 clause b) |
| 21 | `STMT-22` | THE FIT BOUNDARY — "does this tier HAVE a run?" | §3.4.1 |
| 21 | `STMT-21` | adopted by SHAPE, not by spelling | §3.4 |
| 21 | `STMT-20` | the monad layer ORDER is load-bearing | §3.4 |
| 21 | `STMT-19` | the uncatchability invariant is TYPE-level, never lemma-level | §3.4 |

**Grouped, the answer is sharper and it is one place:** `§3.4` — the monad and
outcome substrate contract — carries **9 ungated laws at 21 citations**
(`STMT-14` through `STMT-22`), against `§8.5`'s single law at 24 and `§9.2`'s
three at 13. The most-reached-for unenforced section in the tree is the one
every tier's refusal vocabulary is built on.

### The rule that failed first, and it was mine

`cited_by` began as pure citation-matching, which filed **every law homed in a
script as NO GATE** — `tools/triad.sh` does not cite its own path. A law whose
home *is* a script is gated **by identity**. The self-test caught it on a
fixture before the live run, which is the only reason the first published
number was not wrong by the whole register.

### Triad

`bash -n` clean. `--self-test`: **17 ok, 0 failed**, on a synthetic law index
— row parsing including a non-id row that must be skipped, the register, the
tools list, all three token shapes (`§`, script path, dated ledger id), gated
vs ungated, gated-by-identity, ledger counting across files, and the demand
ordering itself. Live: **~50 s** over 332 laws, which is an audit-cadence cost,
not an inner-loop one. Docs-first: §9.7 names the instrument and carries both
honesty clauses; the tools list gains its row. `docs_check` **87/87**. No Lean
executed.

---

## 2026-08-23-qol-21 — `tools/substrate.sh`: §3.4 gets a gate, and it checks by SHAPE

`laws.sh` picked the target and this closes the loop on it: §3.4 was the
most-cited home in the tree with **no gate at all** — nine laws at 21 ledger
citations — and it is the contract every tier's refusal vocabulary is built
on. Coverage moved **206 → 216 cited, 126 → 116 NO GATE**, and `STMT-19..22`
plus `STMT-67` now name `substrate.sh` as their gate.

### The live table

| tier | monad | refusals | uncatch | run | adequacy |
| --- | --- | --- | --- | --- | --- |
| Ada | NONE | 0/1 | no | NO | — |
| C | BY-SHAPE | 2/6 | no | NO | TWINS? (alloc / allocZeroed) |
| Circuit | NONE | 0/1 | no | yes | — |
| Es | BY-SHAPE | 5/3 | no | yes | TWINS? (envCreate…) |
| Go | **ADOPTED** | 2/0 | no | NO | — |
| Python | **ADOPTED** | 6/82 | **yes** | yes | **OWED** (runScriptClock / runScriptClockMono) |
| Rv | NONE | 0/0 | no | NO | TWINS? (rowCsr / rowCsrI) |
| Sv | **OWN** | 0/17 | no | yes | — |
| SoftFloat, Spice, VerilogA | NONE | 0/0 | no | NO | — |

Calibration held on every tier the dispatch named — Python ADOPTED with
adequacy OWED, Go ADOPTED, C and ES BY-SHAPE, SV OWN — **with one divergence
reported rather than fitted: Ada is `NONE`, not BY-SHAPE.** `LeanModels/Ada/`
is 498 lines of `Ast`/`Json`/`Load` with **no evaluator at all**, so there is
no monad to have a shape. If adoption is ticketed, it is ticketed against
something that does not exist yet.

### Four defects, each found by the tool disagreeing with the calibration

1. **Python read `OWN`.** The ADOPTED test spelled the pre-`:=` part as
   `[^:=]*`, and a binder like `(σ : Type)` **contains a colon** — so the
   pattern could never match a parameterised abbrev, and `abbrev PyM (σ : Type)
   := SemM σ PyErr` fell through to the verdict-type branch. The tier most
   committed to Core read as the tier that rejected it.
2. **A signature spans lines.** `callIn`'s return type `: Run World RVal` is on
   its **second** line, so a single-line rule never compared return types and
   paired anything whose binders matched.
3. **A magic threshold was doing invisible work.** Twins required
   `length(sig) > 24` and the fixture landed on **exactly 24**. Replaced by a
   shape rule — three typed binders and a return type — which is auditable.
4. **Signature identity is necessary, not sufficient.** With it fixed, `alloc
   / allocZeroed` and `envCreateImmutableBinding / envCreateMutableBinding`
   came back as "two semantics". They are siblings, not rivals. So the verdict
   splits: **`OWED`** when the pair also carries a second-implementation marker
   (`Mono`, the naming this repo actually uses for a rebuild twin), and
   **`TWINS?`** — a candidate for a human — otherwise. The marker list is named
   in the source as a *convention, not a law*, so the next lane can see what
   the verdict rests on.

### The bound, stated before the numbers

This greps text. `BY-SHAPE` is a claim about **syntax**, `ADOPTED` about an
**identifier**, and neither is a type-checked equality. A green row is evidence
that **nothing here contradicts §3.4** — never that §3.4 holds. Same direction
of error as `laws.sh`, and said in the same place: before the table.

### Triad

`bash -n` clean. `--self-test`: **20 ok, 0 failed** on a synthetic tier tree —
Core excluded, all four monad verdicts including **the ES trap** (a tier
defining Core's *name* is BY-SHAPE, not ADOPTED), the fit boundary in both
directions, twins by signature with adequacy found and OWED, the marker rule
accepting `callIn/callInMono` and rejecting both real false positives,
uncatchability by pattern, and refusal counting. `laws.sh` **17 ok**,
`docs_check` **87/87**. Docs-first: §3.4 names the gate and carries the first
run; the §7 tools list gains its row. No Lean executed.

---

## 2026-08-23-qol-22 — sites.sh gets a budget and `--arms`, and the timeout did NOT reproduce

### The measured cause, and it is not what was guessed

The report was `sites.sh CallPlan builtin` running past two minutes and being
killed. **On this clone it completes in 5.8 s.** I could not reproduce it, so
I profiled the phases instead of guessing:

| phase | measured |
| --- | ---: |
| `scan_sites` (357 files) | **6 s** |
| `declaring_types` | **2 s** |
| the per-file `awk` **spawns** alone (357 of them) | **~1 s** |
| the character-walking **comment stripper** over 133,147 lines | **~5 s** |

So of the two guesses, **the awk spawn is not the cost (~1 s) and the comment
stripper is** — it is the dominant term, and it is still only 5 s. `.builtin`
has **25 hits in 7 files** against `.unsupported`'s 1383 in 105, so hit volume
is not it either.

**What I cannot rule out is the machine.** This box was at load 19–33 earlier
today and 8.4 when I measured; a 6 s job at load 30 is plausibly a 20 s job,
and a slower or larger clone could go further. That is §5.4a exactly — *a
timing measured on a twin* — so the honest report is: **5.8 s at load 8.4 on
357 files at `4b595c1`, and the two-minute run is unexplained.** If it recurs,
the new progress line will say which file it is on.

### What landed anyway, because the fix is right regardless

**A budget.** `--budget` (default 60 s), and past it the scan stops and prints
`PARTIAL — stopped after Ns at file K of N. Every count below is a FLOOR, not
a bound.` A pricing run that never returns is worse than a slow one, because
the lane cannot tell *expensive* from *hung* — and it then gets killed, which
yields **no number at all**. A partial answer that says so beats a silent
truncation.

**Progress**, every 40 files to stderr, so a long run names where it is.

**`--arms <fn>`** — the pricing question lanes keep answering by hand. Arms are
where a constructor change lands, so this is the per-function form of what the
site census does per type.

### Calibration, and one honest divergence

| function | top-level | total | if/then | lines | hand count |
| --- | ---: | ---: | ---: | ---: | --- |
| `iterValues` | **7** | 15 | 0 | 36 | 7 ✓ |
| `applyCallPlan` | **9** | 13 | 2 | 46 | 9 ✓ |
| `applyBuiltin` | 45 | 76 | 0 | **213** | "~210-line ite chain" |

My first version reported **15** and **13** — it counted **nested** arms, and
the hand counts are the **principal dispatch**. Both are real destructuring, so
both are reported: *an arm count without its depth is the same ambiguity
`laws.sh` hit between a law and its home.* On `applyBuiltin` the line count
matches (**213** ≈ "~210") but the shape does not: it is a **45-arm match
chain with zero `if/then`**, not an `ite` chain. Reported as measured.

### Two defects of my own

An apostrophe inside a comment in a **single-quoted awk program** closed the
program — bash then parsed awk source. And my first `--arms` self-test read
fields `$3..$6` of a five-field record; the tool was right and **the test was
wrong**, which is the second time this lane has had a fixture at fault rather
than the code.

### Triad

`bash -n` clean. `--self-test`: **36 ok, 0 failed** (25 → 36, **11 new**) — the
budget in both directions with the stop point named, and `--arms` on a
synthetic function with a **nested** match and an `if/then`, the block ending
at the next top-level, a missing function, and a doc comment containing a fake
arm. `docs_check` **87/87**. No Lean executed.

---

## 2026-08-23-qol-23 — the successor lane was right twice: `--arms` inverted a shape, and a `no` now names its pattern

### (a) `applyBuiltin` — I measured the right definition and read it wrong

**There is exactly one definition** (`grep` over the tree: `Monadic/Eval.lean:257`,
and one each for `iterValues` and `applyCallPlan`), so we measured the same
function. The disagreement was about its **shape**, and the successor lane —
who read the source — was right. Two defects:

1. **The `if/then` detector missed the chain entirely.** My regex required a
   character after `then`, and in `if fname == "len" then` the `then` is at
   **end of line**. Zero matches. So a 19-deep chain reported `0 if/then`.
2. **Nested match arms were counted as top-level.** The "shallowest depth"
   heuristic finds the shallowest `|`, and in an if-chain the `|` arms live
   *inside* the branches — so 45 nested arms were reported as the dispatch.

**Why that is not cosmetic**, in the lane's own words: a shape report that
inverts ite and match **sends a prover to a tactic that cannot apply** —
`cases` on a `String`. The tool was arguing for the wrong proof.

Now, and matching their verbatim reading exactly:

```
LeanModels/Python/Monadic/Eval.lean:257  if/else-if chain  19 deep (1 if + 18 else-if), 21 then-tokens in all,
                                                           15 on `vs` of 30 match block(s), 45 nested arm(s), 213 lines
```

**The shape is now read from what comes FIRST, not from what is more
numerous** — reading beat counting, so the tool records the order. And three
units are kept apart, because they answer different questions: **30** match
tokens in all, **15** on the dispatch argument `vs` (the successor's number),
**45** arms nested inside them. A count without its unit is the same ambiguity
`laws.sh` hit between a law and its home.

**Every definition is printed.** `arms_of` no longer stops at the first hit per
file, and a name resolving more than once prints `N DEFINITIONS resolve to this
name — all of them:`. That was the identifier law failing inside the tool
again, and it is now a self-test row.

The shape is reproduced as a **calibration fixture** — a 19-deep chain with 15
`match vs with` blocks carrying 45 arms — so the inversion cannot come back.

### (b) substrate.sh: a `no` names its pattern

`Go run NO` was not actionable: a tier could dispute the verdict but not the
reason. Every `no` now carries a tag, and the patterns are printed under the
table:

```
  [U] uncatch   (theorem|example|lemma|#guard) ... (tryCatch|catchIn|.catch), or
                tryCatch within 2 lines of (Loud|Halt|unsupported)
  [R] run       ^def (toRun|run)\b
```

with the header saying **"dispute the PATTERN, not the verdict."** Checking my
own `Go run NO` against its now-visible pattern: Go has `execStmt` and
`execSeq`, neither named `run` nor `toRun` — so the NO is a statement about
the **pattern's** reach, exactly as it should be, and Go can now say so.

### The hang was localized correctly, and I profiled that path

The hang was the **constructor-site mode** (`sites.sh CallPlan builtin`) — which
is the path I profiled: `scan_sites` **6 s**, `declaring_types` **2 s**, the 357
awk spawns **~1 s**, the comment stripper **~5 s**, total **5.8 s**. Still not
reproduced; the two-minute run remains unexplained, and the progress line will
name the file if it recurs.

### Triad

`bash -n` clean. `sites.sh --self-test`: **42 ok, 0 failed** (36 → 42) —
including the five calibration rows. `substrate.sh --self-test` **20 ok**.
`docs_check` **87/87**. No Lean executed.

---

## 2026-08-23-qol-24 — gate DESIGNS for the two head homes, and one of the ten needs no gate at all

Designs only — nothing built. Each carries its honesty clause **first**,
because what a check cannot see decides whether it is worth building.

### §9.2 — consolidation by touch

**PROOF-38 · CONSOLIDATION BY TOUCH, never big-bang; byte-identical across
the move.** *"A lane converts its own artifact the next time it opens that
artifact for any other reason, in the same landing — no deadline, no sweep,
and the test is that the committed output is byte-identical before and
after."*

> **CANNOT SEE** whether the lane had another reason to open the file. It sees
> only whether the diff contains changes *beyond* the conversion — a proxy
> that misses a lane which opened the file to read it.

Reads the staged diff for a **conversion signature**: a file that newly
imports or calls a shared helper (`censuskit`, `tools/triad.sh`, a `Core`
loader). Reports each conversion as **BY-TOUCH** (the file has other changes
too) or **SWEEP** (the conversion is the file's only change), and for a
converted census instrument runs its existing `--compare` to check the
committed JSON is unchanged — the byte-identical half is a composition of a
contract that already exists, not new machinery. **A violation is two or more
SWEEP conversions in one landing.**

**PROOF-39 · port the SUCCESSOR; keep the predecessor as the record of what
it fixed.** The measured failure is precise: a harvesting tier inherits a
known-fragile mechanism *silently*, "**because the predecessor is not marked
as superseded — it is merely older**" (`py_loop`'s Miller-pattern unification,
replaced by `py_vcgen`, both still in the tree).

> **CANNOT SEE an undocumented supersession.** If no prose records that B
> replaced A, nothing can find it — two generations nobody wrote down are
> invisible to a grep.

So the gate is a **marking** gate, not a discovery one. Reads `docs/**` for
supersession claims naming two artifacts, and reads those artifacts' headers.
Reports the pairs and whether the predecessor carries a `SUPERSEDED BY <x>`
marker. **A violation is a documented supersession whose predecessor is
unmarked** — exactly the silent-inheritance case.

**PROOF-40 · the migration must never cost more than the defect it removes.**

> **NO GATE POSSIBLE.** "Cost" here is a judgement over future lane-time and
> build invalidation. The only mechanical proxy is the net line delta — and
> that is the half that was never in dispute. A gate reporting *"net −300
> lines, proceed"* would license a migration that saves 300 lines and
> invalidates every lane's build, which is precisely the trade §9.6 measured
> and **REJECTED** for the shared workspace (0.43 GB a lane against spine-touch
> invalidation at 8 spine moves in 60 commits).

What is worth having is a **report, not a gate**: fold net delta and
spine-touch count into PROOF-38's output, so the arithmetic is visible to the
human who owns the judgement. `laws.sh` should record PROOF-40 as
**`ungateable: cost is a judgement over lane-time and build invalidation; the
only mechanical proxy is the half never in dispute`** so it stops surfacing as
debt.

### §2.4 — thin siblings, and clauses 3 and 4

**MEAS-28 · duplication policed by an instrument, not by discipline.**

> **CANNOT SEE semantic duplication under different spellings** — two loaders
> doing one job with different names and shapes read as two different things.

The most directly gateable of the ten, because the law literally asks for an
instrument: read `harness/*.py` and the tier loaders for repeated *contracts*
(a `git_rev` helper, a `--compare` path, an envelope loader), report how many
independent implementations each contract has with file:line for each. **A
violation is a contract implemented more than once where a shared helper
already exists** — which is `docs/duplication-audit.md` run continuously
rather than by hand every ten landings.

**STMT-59 · THIN SIBLINGS OVER A THICK SHARED TRUNK.** The law states its own
test: *"if a sibling is thick, either the editions really do differ that much
(measure and prove it) or the census was not run."*

> **CANNOT SEE whether thickness is justified.** It can only pair the
> thickness with the presence or absence of a conviction record.

Reads `LeanModels/<Lang>/<Ver>/` against its trunk `LeanModels/<Lang>/` and
reports each sibling's size as a fraction of its trunk, beside the census
artifact convicting its files. **A violation is a sibling over the threshold
with no census naming its contents** — the *"census was not run"* branch, made
visible. (Today this has one row, `C/C23/`; it is a tripwire for the next lane
rather than a finding about this one.)

**STMT-60 · no definition takes a version parameter.**

> **CANNOT SEE a version smuggled as a `Nat` or `String`.** A definition taking
> `(v : Nat)` that means the edition is invisible to a type-based rule, and
> that is the spelling someone reaching for the forbidden thing would use.

Reads every `def`/`abbrev`/`structure` signature under `LeanModels/` and
reports any whose parameter list contains a binder whose **type** is an
edition or version type. **A violation is exactly that** — cheap, sharp, and
worth having despite the hole, because the honest spelling is the one it
catches.

**STMT-62 · THE ONE HONEST FORK — an arity change forks type and consumers.**

> **CANNOT SEE whether a shared consumer is unsound.** A consumer handling
> both shapes through a deliberate wrapper looks identical to one that forgot
> to fork, so this reports **candidates**, never violations.

Composes with `tools/sites.sh`: compare constructor **arities** of the
same-named type across trunk and sibling, and where they differ, ask sites.sh
whether the destructure sites are forked per edition or shared. Reports each
differing-arity type with its consumer split. **The candidate to look at is a
differing arity with a shared consumer** — the `PyErr` shape (3.9's two
nullary constructors against 3.11's three-way split).

**STMT-63 · the edition parameter's granularity is language-decided.**

> **CANNOT SEE whether the granularity is CORRECT for the language.** That is a
> fact about the language's own spec, not about our tree. This checks our model
> against **our own recorded claim**, and nothing more.

Reads each tier's envelope schema and loader for where `language_version`
sits — one per build, or one per file — and reports the granularity each tier
encodes beside the granularity its charter claims. **A violation is a tier
whose charter says per-file while its envelope carries one version for the
whole build**, which is Go's measured case (`//go:build go1.N` overriding the
`go` line per file, verified in both directions from one compiler invocation).

### My own pair — and they are not ungated at all

**MEAS-60** (*an empty diff measured nothing*) and **OPS-46** (*less scope,
ZERO invention*) are **both already implemented in `tools/triad.sh`** —
verified: the `NOTHING STAGED OR COMMITTED` fallback and the hyphenated-
`Examples` widening. They surface as NO GATE because **`laws.sh` attributes by
home token, and their home is a backlog entry id that no tool cites.**

That is not a gate-design problem; it is an **attribution defect in
`laws.sh`**, and it means **the 116 is too high by an unknown margin** — every
law whose durable home is a ledger entry rather than a `§` or a script is
mis-filed the same way. Two fixes, both cheap: extend the law-index home
column to name the implementing script (identity attribution already works),
or have `laws.sh` accept a law's **hook phrase** as a second token. I would do
the first — it puts the fact where a reader of the index sees it.

**Recommended build order, if these are ruled in:** MEAS-28 and STMT-60 first
(sharp, cheap, immediately true), then the `laws.sh` attribution fix (it
corrects a headline number), then PROOF-39, then STMT-59. PROOF-40 is recorded
as ungateable; STMT-62 and STMT-63 are tripwires whose evidence is thin today.

---

## 2026-08-23-qol-25 — the attribution fix: the headline held, the DISPATCH was wrong

Ruled first because a dispatch chosen off a wrong number is the motivated-error
law pointed at ourselves. It was wrong — **not in the headline, in the
ranking.**

### The defect: `§9` matched `§9.5`

Attribution matched home tokens by **substring**, so a law homed at `§9` was
credited to every tool mentioning any `§9.x` — **seven tools for one law**,
including `ada_round_trip.py`. **That is the identifier law failing inside the
instrument that measures enforcement**, and it is the third time this lane has
met it: `sites.sh`'s `.unsupportedDevice`, `arms_of`'s first-hit-per-file, and
now this. Same fix each time — require a boundary.

The ledger *citation counts* used the same loose match, which is where the
damage was.

### The numbers: headline held, ranking inverted

| | before | after |
| --- | ---: | ---: |
| cited by a tool | 216 | **215** |
| ungateable (recorded, not debt) | — | **1** |
| NO GATE | 116 | **116** |

The headline barely moved because false credits and two newly-attributed laws
nearly cancelled. **The demand ranking did not survive:**

| home | before | after |
| --- | ---: | ---: |
| `§9.2` (PROOF-38/39/40) | **14** — the head | not in the top six |
| `§2.4` and its clauses | 7 | **8, and seven ungated laws** |

§9.2's 14 was mostly `§9.x` mentions. **§2.4 is the head by breadth and by
count**, which means the ruled order — MEAS-28, STMT-60 (both §2.4), then
PROOF-39 (§9.2) — is now *better* supported than when it was ruled, and
PROOF-39 sits lower than it looked.

### Two mechanisms, both cheap

**Attribution by identity when the home names a script.** `MEAS-60` and
`OPS-46` were never ungated — both are implemented in `tools/triad.sh`
(verified) and were invisible because their home is a ledger entry id no tool
cites. Their index rows now carry `— gate: tools/triad.sh`, and identity
attribution (which already worked) does the rest. **34 laws are homed in a
ledger entry**, so this channel exists for all of them.

**`ungateable: <reason>` in the index home column**, reported in its own
bucket. Re-surfacing a settled finding every audit is how it gets
re-litigated. `PROOF-40` is recorded with the ruled sentence: *cost is a
judgement over lane-time and build invalidation; the only mechanical proxy is
the half never in dispute.*

### A cost regression, caught and fixed before landing

The boundary fix built one regex **per token per file** and doubled the run —
**50 s → 1 m 51 s**. Hoisted to once per token: **54 s**. A tool that prices
enforcement has to be priced too, which is the lesson `sites.sh` took a
budget for.

### Triad

`bash -n` clean. `--self-test`: **22 ok, 0 failed** (17 → 22) — `§9` not
matching `§9.5` while `§9.5` does, a dated id not matching its longer sibling,
and an ungateable row recognised with its reason. Doc-first: §9.7 carries the
correction and says the dispatch moved rather than the headline. `docs_check`
**87/87**. No Lean executed.

---

## 2026-08-23-qol-26 — MEAS-28 gets its instrument: duplication counted, not remembered

The one law in the tree that **literally asks for a tool**, and it had none.
`docs/duplication-audit.md` measured the census contract implemented **14
times** — by hand, every ten landings, which is exactly what the law forbids.

### First run, 39 Python files

| contract | count | status |
| --- | ---: | --- |
| `--compare` | **15** | DUPLICATED — `censuskit.py` proposed, not landed |
| `census` main | **15** | DUPLICATED |
| double-run | **10** | DUPLICATED |
| self-test | **10** | DUPLICATED (none proposed) |
| `git_rev` | **8** | DUPLICATED |

### Two channels, and the `git_rev` row proves why both are needed

**CONTRACTS** (curated shapes) finds **8** files running `git rev-parse`.
**NAMES** (mechanical, every top-level `def` in more than one file) finds **3**
called `def git_rev`. So **five implement the contract under another name** —
`_git`, `_read`, inline — which is precisely the duplication a name-based rule
misses and a contract-based one catches. Each channel finds what the other
cannot, and neither alone would have reported 8.

The mechanical channel also surfaced rows no curated list had:
`_reexec_under_pinned_frontend` ×4, `_read` ×4, `classify` ×6.

### A duplicate is not automatically a violation

§9.2 consolidates **by touch**, so the tool separates **`DUPLICATED`** (work
*available* — no shared helper has landed) from **`VIOLATION`** (work
*refused* — the helper exists and is not being used). Today every row is
DUPLICATED, because `harness/censuskit.py` is still a proposal. That means the
instrument currently reports **opportunity, not debt**, and it will flip to
VIOLATION the moment the helper lands — which is the right way round: the
count becomes a red only once ignoring it is a choice.

### The honesty clause is in the header, not the footnote

> **CANNOT SEE semantic duplication under different spellings.** Two envelope
> loaders doing one job with different function names, argument orders and
> local variables read here as two different things. The duplication that cost
> this repository most was found by a human reading four loaders side by side,
> and that reading is not automated here.

So every count is a **floor**, in the same direction every other instrument in
this tree errs.

### Triad

`bash -n` clean. `--self-test`: **9 ok, 0 failed** — files found across both
directories, a contract implemented twice, a contract nobody implements, a
name in three files and one in two, a unique name correctly *not* reported,
and the DUPLICATED/VIOLATION flip turning on whether the helper file exists.
Doc-first: §2.4 names the gate and carries the first run and the two-channel
argument; the §7 tools list and the law index gain their rows. `docs_check`
**87/87**. No Lean executed.

---

## 2026-08-23-qol-27 — `tools/editions.sh`: STMT-60 and STMT-59 gated, and STMT-61 has nothing to compare

### STMT-60 — clean, and the one hit is clause (4)'s legitimate case

**Zero violations.** The only definition in the tree with a version-typed
binder is Go's `perIterationLoopVars (v : LangVersion) : Bool`, and it is
reported as **`clause-4`**, not as a violation: §2.4(4) records that for Go
the edition is a property of the **file**, carried as data, so a predicate
**classifying** that data is not a semantics parameterised by edition.

The discriminator is the **return type** — a plain `Bool`/`String`/`Nat`
classifies, a monad or a value computes — and the tool prints the list so a
lane can **dispute the list rather than the verdict**. The header states the
hole up front and the report repeats it every run:

> **CATCHES THE HONEST SPELLING ONLY.** A version smuggled as a `Nat` is
> invisible to a type-based rule, and that is the spelling someone reaching
> for the forbidden thing would use.

### STMT-59 — and it convicts the section's own tier

```
  LANG   VER     SIBLING    TRUNK  RATIO  THEOREMS CONVICTED-BY
  C      C23        2213      732   3.02    7/0    clauses only: c-construct-census.json (no census names the FILES)
```

**The sibling is three times its trunk** — the inverse of *thin siblings over
a thick shared trunk* — and **no census names its files**. §2.4(1) asks for a
measurement convicting the **FILE**; a C construct census exists, and it
convicts clauses. Which of the law's two branches applies (*"the editions
really do differ that much"* or *"the census was not run"*) is the C lane's
call — the gate's job was to make the question unavoidable, and it does.

### STMT-61 — measurable, and there is nothing to measure

The design was a statement-shape comparison across trunk and sibling. **It
holds mechanically and would report zero forever**: measured before building
it, the C trunk holds **0 theorems** and the C23 sibling holds **7**. A
duplicate-finder needs a trunk theorem to duplicate.

So the failure mode in this tree is not *"proved twice"* — it is **"proved
only in the sibling"**, which is the same evidence read the other way round.
That is now a **column** (`THEOREMS 7/0`), not a comparison that cannot fire.
The law index records the mechanism and why it is not built. **This is the
STMT-62/63 rule applied to a third law: a gate whose evidence row does not
exist yet is a design, not a build.**

### Two false attributions caught before landing

The conviction lookup first credited C23 to **`ada-suite-census.json`** — a
coincidental token match against a test name — because it took the
alphabetically first JSON containing the string. Anchoring the filename to the
tier fixed it; the glob `*c*` had matched the word *census* in every file in
the directory. And it now separates **`FILES:`** from **`clauses only:`**,
because saying *"no census"* when a clause delta exists is as wrong as saying
the file is convicted.

### Triad

`bash -n` clean. `--self-test`: **12 ok, 0 failed** — a version binder found,
a `Bool` return classified as clause-4, a semantic return as a VIOLATION with
its return type named, an `Edition` binder counted, a def without one silent,
prose about one ignored, and the sibling walk with its line counts, theorem
split, and a non-edition directory correctly not treated as a sibling.
Doc-first: §2.4 names the gate and carries the C23 finding; the §7 tools list
and three law-index rows updated. `docs_check` **87/87**. No Lean executed.

---

## 2026-08-23-qol-28 — `--axioms` dropped the last name, and the absence was silent

Reported by the fuelMono lane, reproduced immediately, and it is my defect.

`printf '%s' "$AXIOMS" | tr ',' '\n' | while IFS= read -r d` — **without a
trailing newline `read` returns non-zero on the final partial line, so the loop
body never runs for it.** Measured:

* `--axioms 'A,B'` appended **only `A`**;
* `--axioms 'OneName'` appended **nothing at all**.

And `axiom_report` opened with `grep -q … || return 0`, so a run that printed
**no axiom line whatever** said nothing and left the verdict `TRUSTWORTHY`.
A bogus name never reached Lean, so it never errored — where a plain
`lake env lean` on the same `#print axioms` is exit 1.

**Since `9dae608` made this flag the evidence standard, every single-name
`--axioms` verdict has been unverifiable and looked green.**

### It is this tool's own law, firing on the guard built to enforce it

`qol-19` landed `--axioms` under the statement *"a success signal that survives
the failure it should report"*. The guard then did exactly that: the absence of
the evidence it existed to collect **read as success**. `cc497eb`'s law —
absence is not zero — was needed against the code that quoted it.

### The fix, and the guard that makes it self-reporting

`printf '%s\n'`, extracted into `append_axiom_prints` which **returns the
count appended**; and `axiom_report` now takes the number of names **requested**
and **refuses loudly** when the axiom lines printed do not equal it:

```
    axioms         REFUSED — 2 name(s) requested, 1 axiom line(s) printed.
                   ABSENCE IS NOT ZERO: a name that produced no line was never
                   checked, so a verdict quoting this run is unverifiable.
```

A refusal **voids the verdict** (`NOT A MEASUREMENT: the axiom section
refused`), so the flag can no longer report green while under-collecting. A
clean run now states its own coverage — `axioms 2 of 2 requested` — rather than
printing lines whose completeness the reader had to assume.

### Triad

`bash -n` clean. `--self-test`: **85 ok, 0 failed** (74 → 85, **11 new**) — the
single name appended and present, the last of several not dropped, an empty
element skipped without being counted, and the count guard in four states:
1-of-1 reported, 2-requested-1-printed refused with a nonzero exit and the
absence-is-not-zero line, and **1-requested-none-printed refused — the case
that used to be silent.** No Lean executed; the guard is a function of
`(log, verdict, count)`, which is also the only way to test the failing cases.

**Owed to every lane:** any `--axioms` verdict quoted since `9dae608`,
especially a single-name one, should be re-run before it is relied on.

---

## 2026-08-23-qol-29 — the merge driver configures itself, and a green build's axiom ledger survives

Two frictions the R-track lane measured, both mine to fix.

### (1) A driver nobody configured

`docs/backlog/INDEX.md` is **generated and committed**, so it conflicts on
every lane's rebase — **two conflicts in one day for one lane**, and every lane
pays it. `qol-14` landed a merge driver for exactly this and then left the last
step to a human: **git ships no `ours`-style driver, and config is per-clone.**
So the declaration sat in `.gitattributes` doing nothing, in every clone but
mine.

**A fix that needs a human to type it is not a fix.** `tools/triad.sh` and
`tools/check.sh` now call `tools/backlog-index.sh --ensure-driver` on their
first run in a clone — one line when they configure it, **silence afterwards**:

```
  merge driver: configured merge.backlog-index.driver=true — .gitattributes names
  it and git does not ship it, so docs/backlog/INDEX.md will resolve instead of
  conflicting
```

Three details worth the words. The driver is **renamed from `ours` to
`backlog-index`**, so a lane reading `git config --get-regexp '^merge\.'` sees
*why* it is set rather than a generic take-ours. The name is **read from
`.gitattributes`**, never from a constant in the script — two places naming one
driver is the defect `dupes.sh` exists to count, and a self-test row renames
the attribute and checks the tool follows. And the helper lives in
`backlog-index.sh` with both gates **calling** it, rather than the same six
lines pasted into two scripts.

### (2) A green build stopped naming its own evidence

The in-file `#print axioms` ledger is the **house standard** for library files
— it is in the tree, it runs under a tenure, and it is immune to
`check.sh --axioms` by design. But the build writes to a `mktemp` log named only on
**red**, so on **green** the evidence was produced and then left unreferenced:
the one outcome in which anybody wants to quote it.

`TRIAD DONE` is now preceded by the salvage, labelled so it is quotable:

```
[11:56:03] axiom ledger, from this build:
[11:56:03]     'thm' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Red is unchanged — the whole log is kept and named, as before.

### (3) And the refusal says which evidence path to use

`check.sh --axioms` is for **scratch files only**, and `refuse-library` is by
design rather than a gap. After `qol-28` — where that flag's own evidence was
silently incomplete — a refusal that does not name the alternative invites a
lane to reach for the flag anyway. It now says: *"LIBRARY FILE: the in-file
`#print axioms` ledger via a tenure is the evidence path — `--axioms` is for
SCRATCH files, and this refusal is by design, not a gap."*

### Triad

`bash -n` clean on all three. `triad.sh` **161 ok** (156 → 161: a green log
yielding its axiom lines under a label, a log with none saying nothing and
reporting it), `backlog-index.sh` **34 ok** (25 → 34: nothing declared, name
read from the attribute, declared-but-unset configuring and saying so, already
set staying silent, and a **renamed** driver followed to its new name),
`check.sh` **87 ok** (85 → 87: the refusal naming the evidence path and saying
it is by design). Live: a dry-run configured the driver with one line and the
next run was silent. Doc-first: §9.5 carries the auto-config; the §7 tools list
gains the row. No Lean executed.

---

## 2026-08-23-qol-30 — correction: the build log was never deleted, only unnamed

The R-track lane corrected my `qol-29`, and the correction shrinks the fix.

**`tools/triad.sh` never deletes `BUILD_LOG`** — verified, there is no `rm` of
it anywhere in the script. A green tenure merely stops **referencing** it. My
entry said the evidence was *"abandoned"* and *"thrown away"*; the file
persists, and the entry is corrected in place.

**But losing the path is enough to lose the evidence**, and the measurement
says why: **56 `triad-build.*` files coexist in one `TMPDIR`** right now, from
many lanes and many runs. The most recent is timestamped four minutes before I
looked and is very plausibly **another lane's**.

So the fix is smaller than preservation — **name the path on green as well as
on red** — and the line carries its own caveat, because the advice is only
needed by a reader who no longer has the line:

```
full log: …/triad-build.f2OSEj  (kept, not deleted — recover by THIS PATH;
55 other triad-build logs share this TMPDIR, so the NEWEST is probably
another lane's)
```

The count is computed live rather than asserted, so it stays true as the
directory fills. The axiom-line echo from `qol-29` stays: it is the half a
lane quotes, and it costs nothing.

**The doc carries the recovery rule** (§9.5): recover by the printed path,
never by *"the newest"*; and if the line is gone, select by mtime **inside
your own tenure's window** — the tenure-open and `TRIAD DONE` lines bracket it
— rather than by recency alone. Selecting by recency across 56 files is
selecting somebody else's evidence.

### Triad

`bash -n` clean. `triad.sh --self-test`: **165 ok, 0 failed** (161 → 165) — the
pointer naming the log, saying it was kept rather than deleted, **counting the
other logs beside it**, and warning off the newest. `docs_check` **87/87**. No
Lean executed.

---

## 2026-08-23-qol-31 — the vendored-fixture convention, and a prose mention that still cost the whole library

The Go lane asked me to finish the convention my classifier fix started. Doing
it found the fix was **half done**.

### The gap: an attribution header re-created the 37-minute tenure

`qol-5` made an *unreferenced* non-Lean fixture classify `docs`. But the
reachability probe grepped the raw `.lean` text — so a fixture named in a
**docstring** counted as referenced, and a referenced fixture widens the build
to the whole `Examples` library. Reproduced before fixing:

```
  build     lake build Examples.go.probe.guards Examples     <- the 37 minutes, back
```

**And an attribution header is exactly what makes a lane name the file in
prose**, so the convention I was asked to document would have fought the rule I
was documenting it against. The probe now **strips Lean comments** before
looking — the same discipline `wasm_sorry_census.py` needed for `sorry` and
`sites.sh` for constructor sites. After:

```
  build     lake build Examples.go.probe.guards
```

A **code** reference (`include_str`, `load_c_program … from`) still widens,
verified in the same run.

### Two defects of mine, and the second was live

**The fix was applied to one of two branches.** I made the `git grep` path
comment-aware and left the plain-`grep` fallback blind — so a clone without
git, *and every self-test fixture*, still counted prose. A rule enforced on one
of two paths is a rule with a hole exactly where nobody looks.

**And then variable capture.** My loop was `for c in $(git grep -l …)`, and
`c` is the name `classify_list` holds its verdict in — not declared local. The
loop overwrote `"tier"` with a filename, which fell through the caller's
`case` to `docs`. Live effect: `Examples/c/sunfish/sunfish.json`, which real
code ingests at `guards.lean:43`, classified **docs** — a referenced fixture
read as invisible, from a variable name. Caught by running the live case
rather than trusting 165 green self-tests, which is the only reason it did not
land.

**A fixture was wrong too.** The `qol-5` self-test wrote its "referenced"
reference as a `--` comment. Once the probe learned to skip comments, that
fixture was asserting the opposite of the tree it stood for — it now uses the
real `load_c_program … from` spelling.

### The convention, now in §7

**Vendored fixtures live BESIDE the model** — `Examples/<lang>/<case>/` next to
that case's `guards.lean` — and that is safe now: measured **91 s → 37 min →
129 s**. **The fixture carries its attribution and licence in the file**, on
the Go lane's precedent: BSD-3-Clause, *"Copyright 2009 The Go Authors"*, per
`go-charter.md` §1.4. That is §8 step 0's *licence and provenance are registry
fields* applied to one file instead of a corpus.

### The instruments skip them, explicitly

`sites.sh` scans `*.lean` only; `dupes.sh` scans `harness/` and `tools/` only.
Both already did **by construction** — I checked before claiming a fix — but
neither said so, and an accident that holds is one edit from not holding. The
filters are now commented as deliberate and pinned by self-tests: a `.go`
beside a `.lean` is not in the scan set, and an `Examples/` `.py` fixture is
not counted as a duplicated contract.

### Triad

`bash -n` clean. `triad.sh` **169 ok** (165 → 169: a vendored `.go` beside a
`.lean` classifying docs, **not widening the build**, doing so **even though
the docstring names it**, and a code reference still reachable). `sites.sh`
**44 ok**, `dupes.sh` **10 ok**. `docs_check` **87/87**. No Lean executed.

---

## 2026-08-23-qol-32 — audit HIGHs 1-3 and MEDIUMs 7-8: the matchers learn what a comment is

Four of my twelve audit rows reduce to one sentence: **this matcher does not
know what a comment is, or what a whole name is.** So the primitive moved out
of the tools and into `tools/leanlex.sh`, sourced rather than re-grown —
`sites.sh` and `triad.sh` had a copy each and `substrate.sh` needed a third and
fourth, which is exactly what `dupes.sh` counts and MEAS-28 forbids. The
existing copies retire **by touch** (§9.2), not in this landing.

### HIGH — `laws.sh:104`, a token that could never match its own home

`home_tokens` capped a section at **two levels**, so a law homed at `§3.4.1`
tokenised to `§3.4` — and `tok_regex`'s boundary excludes a following `.`, so
the truncated token **could never match the citation it came from** while
matching every sibling that spells the two-level form. **STMT-22 was credited
32 citations belonging to §3.4.** Now the full dotted section is the token.

**No parent token is emitted**, deliberately: crediting a `§3.4.1` law for a
`§3.4` mention is the over-crediting the boundary work exists to remove.

### HIGH — `substrate.sh:249`, two greps that need not agree

`adequacy_for` ran **two independent unanchored greps over a file**: they need
not land on the same theorem, and with raw names `callIn` is satisfied by
`callInMono` — so one line could satisfy both halves. Now **one declaration**
(comments stripped, continuation lines joined) must name **both**, each matched
as a whole name.

### HIGH — `substrate.sh:143`, match arms counted as declarations

REF_LOCAL reported "locally-declared constructors" while matching **any** line
starting `| unsupported`, including `match` arms inside proofs — the defect
`sites.sh`'s `declaring_types` already documents. It now tracks the inductive
block, and the trailing class is `([ \t(]|$)` so a **nullary** constructor at
end of line is no longer missed.

**The correction is large and it is mine to own: Python's REF_LOCAL was 82 and
is 4.** The number I published in `qol-21` was roughly a **20× over-count** of
match arms. Sv 17 → 11, C 2/6 → 1/7, Python REF_CORE 6 → 5.

### MEDIUM — `substrate.sh:142` and `:154`

REF_CORE now counts **occurrences** (not lines), allows any spacing, strips
comments, and takes the constructor as a **parameter**, so the report matches
the documented `P_REFUSAL` instead of a hard-wired copy of it. UNCATCH requires
the keyword and the catch token in the **same declaration** — the old rule
accepted any `tryCatch` within two lines of the word `Halt`, which every tier
built on `ExceptT ρ (StateT W Halt)` writes constantly.

### Triad

`bash -n` clean. `laws.sh` **26 ok** (22 → 26: a three-level section surviving
tokenising, not truncating to its parent, matching its own home, and a `§3.4`
tool **not** crediting it). `substrate.sh` **25 ok** (20 → 25: prose about
uncatchability not counting as a statement, both spacing variants counted while
prose is not, a nullary declaration counted, and a match arm **not**). The
uncatchability fixture was a `def` and is now an `example`, because STMT-19
asks for a **statement**. `docs_check` 87/87. No Lean executed.

---

## 2026-08-23-qol-33 — audit HIGH 4-5: a regex awk rejected outright, and a guard that failed open

### HIGH — `analogues.sh:49`, and it was worse than the row said

The shape regexes went to awk through `awk -v RE="$re"`, which **strips one
backslash level** — the third time this tree has met that defect. The row says
`\(` becomes a group-open; measured, it does not merely mis-match:

```
awk: syntax error in regular expression (F *:|∀ *F|fuel|Fuel
```

**awk exits.** So `analogues.sh fuel` returned *nothing*, and an empty result
is indistinguishable from a small neighbourhood — the tool whose whole job is
to say *"this shape has 26 proved analogues"* was reporting zero for one of its
twelve shapes, and reporting it silently.

The fix doubles the backslashes at the boundary. **The row that would have
caught it now exists: every named shape must match a known instance**, driven
against a fixture carrying one line per shape. All twelve pass; before the fix,
`fuel` did not.

### HIGH — `a6-guard.sh:35`, failing open on an unreadable machine

The guard's own header carries the sentence **"a check that only prints is not
a guard"**. The audit found the same defect's second half: with `lsof` absent,
failing, or denied, every candidate went down `continue`, `found` stayed 0, and
it exited **0 — "the tree may be rewritten"**.

Now: **probes are checked up front**, an unreadable cwd on a live Lean process
**refuses rather than skips**, and refusal has its own exit code (**2, CANNOT
TELL**) distinct from "a build is here" (1). *Silence from a probe is not
evidence of absence.*

Both readers are mockable, so the **positive case is finally driven** — it
never was. That is what the file's own history warned about: *"found by testing
the POSITIVE case; the negative case passed throughout and proved nothing."*

**One test defect of my own on the way:** `PATH=/nonexistent bash …` cannot
find `bash` itself, so my first missing-probe row measured **127** while
believing it had measured the guard. It uses `"$BASH"` now.

### Not wired into `triad.sh`, and the reason is recorded

The audit's fix suggests calling the guard from triad's rebase/merge
preconditions. **`tools/triad.sh` never rewrites the tree** — it refuses to
build *during* a rebase, which is the opposite direction — so calling A6's
guard there would add a check that cannot fire, which is the audit's own
`vacuous` category. The call site that matters is a lane's **rebase step**, and
this lane now runs it there. Recorded rather than done, per the ruling that a
won't-fix carries its reason.

### Triad

`bash -n` clean. `analogues.sh` **28 ok** (16 → 28, twelve of them the new
per-shape rows). `a6-guard.sh` **8 ok** — its first self-test, covering the
positive case, a build elsewhere, no builds, an unreadable cwd, and a missing
probe. Live on this machine the guard exits 0 correctly. No Lean executed.

---

## 2026-08-23-qol-34 — audit MEDIUM 11 and LOW 12: a ledger that can fail, and a map that reads the tree

### MEDIUM — `triad.sh:848`, the ledger had no failing path

`axiom_ledger` grepped, echoed, and returned 0 whenever **any** axiom line
existed. It never inspected the bracketed list, so **`[sorryAx]` printed
identically to `[propext, Classical.choice, Quot.sound]`** and the tenure still
said `TRIAD DONE … gates green`.

**That is this lane's own law for the third time** — a success signal that
survives the failure it should report — and this time in the guard built two
landings ago to *carry the evidence*. `qol-19` stated it, `qol-28` hit it in
`--axioms`, and it was sitting in the ledger the whole time.

Now the declared standard set is named (`propext Classical.choice Quot.sound`,
AGENTS.md § House rules), every line's list is scanned against it, and anything
outside returns **2**, names the axiom **and the declaration**, and **sets the
tenure's exit code to red**: *"a build carrying these is not a green tenure."*

### LOW — `triad.sh:432`, a comment the tree contradicts

`example_dir_tiers` was a hand map whose header asserted it *"is not
derivable"*, and which claimed `go` had **no** model tier — while
`LeanModels/Go/` is 1,129 lines and every `Examples/go/**/*.lean` says
`import LeanModels.Go`. **A hand-written claim the tree contradicts is the
identifier law wearing a comment.**

The map now **derives from the imports that exist**, falling back to the
explicit table only where nothing is declared. Verified live: `go → Go`, and
`mixed-signal → Circuit Python` — which is *exactly* what the hand map said,
so the derivation reproduces the one row that was genuinely ambiguous instead
of replacing it with a guess.

**Two self-test rows changed rather than the code**, and that is the finding:
they encoded the hand map's errors. `Examples/go/…` now contributes `Go`, and
the row says so. The spice row was made **fixture-driven** — it declares the
imports it means instead of inheriting whatever the live tree happens to have,
because a derived map read from the real tree makes a test drift with every
lane's imports.

### Triad

`bash -n` clean. `triad.sh --self-test`: **174 ok, 0 failed** (169 → 174) — an
off-standard axiom returning 2, naming the axiom **and** the declaration,
saying the tenure is not green; the declared three passing; and
`Lean.ofReduceBool` caught as off-standard. No Lean executed.

---

## 2026-08-23-qol-35 — audit MEDIUM 9-10: a checker with a floor, and a CI that can fail

### MEDIUM — `docs_check.py:81`, a corpus that could shrink to nothing

The default corpus was filtered by `is_file()`, so renaming or deleting
`README.md`, `AGENTS.md` or `docs/` **silently shrank it** — and
`(REPO/"docs").rglob("*.md")` on a nonexistent directory yields nothing without
error. With no floor on `n_checked`, an empty corpus reported a clean check.

Now a missing default **refuses by name**, and `n_checked == 0` over the
default corpus refuses with *"an empty check is an instrument fault, never a
clean tree"* — §5.4's zero-row law, applied to the checker that enforces it
everywhere else. Explicit paths still bypass the floor: a lane checking one
file should not be forced to have blocks in it.

`docs_check.py` gained its first **`--self-test`** (5 rows), and the root is
injectable so the refusals are **driven rather than admired**.

### MEDIUM — `tools/ci.sh:17`, 34 of 39 steps that could not fail

`maybe` turned **any** missing path into SKIP, so deleting `tools/docs_check.py`
or `harness/sv/diff_test.py` left CI green. The discriminator needs no list and
is mechanical: **a file git tracks is not optional.** A tracked path that is
absent is now a **FAIL** (*"a gate file that vanished is a defect, not an
absent simulator"*); an untracked one — a simulator binary, a generated
artifact — stays a SKIP, which is honest.

And **no tool's `--self-test` ran in CI**, so a gate could rot silently between
audits — which is how four of this lane's tools shipped with defects this audit
had to find by reading. There is now a `tool-self-tests` step running all
twelve plus `docs_check.py --self-test`.

### The near-miss in that step, and why it is the interesting part

The first selector was `grep -q -- '--self-test'`, which matched **`ci.sh`
itself** — it mentions the flag in the very function doing the matching — so
the step re-entered CI and started an **unticketed `lake build`**. It hung,
which is the only reason I looked.

Two guards now, and both are load-bearing: the selector matches a **handler**
(`--self-test)` or `= "--self-test"`, the two spellings in this tree) rather
than the string, and an explicit `*/ci.sh) continue` belt. The belt is not
redundant — my own comment inside `ci.sh` now contains `= "--self-test"`, so
the grep matches it again and **the belt is what excludes it**. A tool that
merely talks about a flag does not accept it.

Per-tool `timeout 120`, so a future tool that hangs cannot hang CI.

### Two rows closed without a code change, recorded in the audit file itself

**MEDIUM `triad.sh:497`** was already fixed by `4c710e3` before the audit was
written — verified against the row's own example rather than assumed:
`Examples/go/bitlen/bitlen.go` classifies `docs`, and a code reference still
widens. The `git grep -l` **prefilter** is still a bare-basename match, which
is what line 497 reads — but it only selects candidates and `code_mentions`
decides.

**HIGH `a6-guard.sh`'s triad wiring** is not done, with the reason in the
report: `triad.sh` never rewrites the tree, so the guard there would be a check
that cannot fire — this audit's own `vacuous` category.

### Triad

`bash -n` clean. `docs_check.py --self-test` **5 ok** (new). The CI step runs
green across all twelve tools. `docs_check` **88/88**. No Lean executed.

---

## 2026-08-23-qol-36 — INCIDENT: a self-test that ran CI, 26 deep, on a cold clone

I caused this. `bash tools/ci.sh --self-test` ran the **entire CI**, and its
own tool-self-test step invoked `ci.sh --self-test` again — **26 instances**,
each starting `lake build` with default parallelism, no `nice` and **no
ticket**, in a clone whose Mathlib cache did not exist. Load ~30 on Thomas's
machine for 20+ minutes.

### Why the guard did not hold — and it is my own law

After the *first* near-miss I diagnosed the re-entrancy, added a belt, verified
it green, and **left the hung process running in the background.** That process
had the pre-belt `selftests` in memory and kept spawning.

> **An amendment takes effect when the last script predating it is dead** —
> §7.1a's 16.2, which is in this lane's own ledger, and which I applied to
> other lanes' runners while leaving mine alive.

Worse: I then **edited `ci.sh` repeatedly while 26 instances were executing
it**. §7.1a names that hazard exactly — *bash reads a script INCREMENTALLY, so
editing one that is running corrupts it*. I cannot cleanly separate "ran the
old code" from "read a shifted file", and I am not going to claim I can.

**The honest summary: the guard never failed, because the guard was never in
those processes.** A fix in the source does not stop what is already running.

### Why a cold clone made it a machine-killer

`~/repos/lean-qol` was made with a plain `git clone`, **never A13-seeded** — I
confirmed the absence of `.lake` earlier this session, and `check.sh --iterate`
had been correctly refusing it as **cold** all along. So the accidental build
had to fetch and build Mathlib from nothing: the `.lake` it left behind is
**3.2 GB**. Not an invalidated cache — **a cache that never existed.**

> **An unseeded clone is permanently one accident away from a full Mathlib
> build**, and A13's "27 s and 29 MB" is the price of not being in that state.

### The fix: three layers, because the incident used the one path with none

1. **`ci.sh` takes NO arguments.** Ignoring an unknown flag is how a self-test
   request became a full build. `--self-test` now exits **2** before anything.
2. **An environment sentinel, not an argv check.** `LS_CI_SELF_TEST` is
   inherited by **every descendant at any depth and through any argv** — which
   is precisely what an argv or filename guard cannot do.
3. **The self-test stubs `lake`.** Under the sentinel, PATH is prefixed with a
   no-op `lake` that exits 97 loudly, so a self-test **cannot reach a real
   build** even if a future edit re-introduces a call. A11: any lake
   invocation needs a ticket or a stub, and a self-test has no ticket.

All three verified live: the incident command exits 2; a pre-set sentinel
refuses; a stubbed `lake build` exits 97. The guards sit at lines 31/51/58,
**before the first `step` at 129**.

`--verify-guards` is the one allowlisted flag, and its handler cannot reach the
CI body. An allowlist is not the defect — **ignoring an unknown flag was.**

### Machine, verified by pid rather than assumed

Killed by pid, mine only: the recursion chain (**26 `ci.sh`**), its `lake`, and
every orphaned `lean` under a `lean-qol` path. Confirmed after: **0 `ci.sh`, 0
lean-qol `lean`/`lake`**, load **~30 → 14**, and the sv, es and c lanes' own
processes (`9282`, `13705`, `31843`, `49734`) **untouched** — base rule 6, kills
by parentage and by path, never `pkill`.

### Owed

`ci.sh`'s own `step "lake-build" lake build` still runs an unticketed bare
`lake` when CI is invoked normally. On a GitHub runner that is fine; **on
Thomas's machine it is not**, and it is shared infrastructure rather than this
lane's to change unilaterally. Flagged for the coordinator.

---

## 2026-08-23-qol-37 — CI's build is gated by host, and this clone is seeded at last

### The ruling, implemented

`ci.sh`'s `lake-build` now runs **only on `GITHUB_ACTIONS=true`**. Anywhere else
it prints the named line and skips:

```
=== [lake-build] SKIPPED on non-CI host — Lean builds go through tools/triad.sh (A11)
```

`--require-build` turns that skip into a **failure** for a caller that must not
proceed without a build — and it is *only* that. **There is no local override
that reaches bare `lake`:** a local caller who wants a build takes a ticket,
full stop.

### One extension beyond the letter, flagged rather than smuggled

Auditing for other bare invocations found **two more**: the spice
`*-adversarial` steps run `lake env lean --run …` directly. A11 says *any Lean
process is Lean execution*, so the reason applies even though the ruling was
written about `lake build`. They now go through `maybe_lean`, which carries the
same host gate. **This extends the ruling; say so if it should not.**

### The rows, and what makes them worth having

*"No lake was invoked"* is asserted, not hoped: the verification stub **records
being called** by touching a marker, so the absence is checked. `GITHUB_ACTIONS`
set → the step runs and the stubbed `lake` fails it; unset → the named SKIP,
recorded as a **skip** not a pass, with **no marker**; `--require-build` → a
**fail**, still with no marker.

**A subshell defect on the way**, and it is the same one this lane has now hit
three times: the first cut called `lake_build_step` inside `$( … )`, so the
`skip+=`/`fail+=` mutations were discarded and three rows read as failures. The
step is called directly with output to a file. And the `maybe_lean` row failed
first because I defined the helper **after** the block that tests it — a guard
tested before it exists is not tested.

### A13, at last — and the number is the argument

The 3.3 GB `.lake` the incident built was **deleted** and the clone **CoW-seeded**
from an idle, untorn peer. Preconditions checked first, not assumed: no build
had either peer as its cwd (by `lsof`), both trees clean, and **toolchain,
`lake-manifest.json` and `lakefile.toml` all identical**.

| | |
| --- | ---: |
| seed time | **13 s** |
| apparent cache | 6.3 G (larger than the accident's) |
| **free disk** | **144 Gi → 147 Gi** |

**A bigger cache that gave back 3 GB** — that is what `-c` buys, and it is A13's
"27 s and 29 MB" reproduced. `.git` was not touched, so none of A13's
branch-or-remote inheritance applies.

**Verified by the tool that had been refusing all session:** `check.sh` on a
scratch file flips from **`refuse-cold`** to **`scratch` — "warm-clone
amendment CHECKED"**, and `--iterate` would now be permitted. The clone is no
longer one accident away from a Mathlib build.

### Triad

`bash -n` clean. `ci.sh --verify-guards`: **14 ok, 0 failed**. The incident
command still exits **2**. No Lean executed by this lane.

---

## 2026-08-23-architecture-27 — INBOUND FROM THE FAMILY-ARCHITECTURE LANE: QoL lane's to renumber or close

*Id kept in the architecture namespace; nothing minted in the QoL sequence.
Filed after reading this file, per §9.5b — the correction below is already
yours and is not being re-reported. Only the residue is.*

### THE `REF_LOCAL` CORRECTION IS OWNED, BUT `qol-21`'s PUBLISHED TABLE STILL READS `6/82`

The `substrate.sh:143` fix (`12386db`) corrected Python's `REF_LOCAL` from
**82 to 4**, and this lane's entry owns it in as many words. **The residue is
the place the number was published**: `2026-08-23-qol-21`'s live table still
shows `| Python | ADOPTED | 6/82 | …`, and a reader of that entry has no way to
reach the correction.

Landed as a norm in `docs/family-architecture.md` §5.4a
(`2026-08-23-architecture-27`):

> **A number a gate PUBLISHED is a SECOND ARTIFACT. Correcting the instrument
> corrects the next run; the published figure is corrected where it was
> published, or it stands.**

**Asked for: an ANNOTATION on `qol-21`'s row, not a rewrite** — §5.4b's
annotation norm, *the measurement was right as taken; only its tense was
wrong*. Something of the form *"corrected `12386db`: 6/4, the 82 was match arms
counted as declarations"* beside the row is the whole of it. The other
corrected figures (Sv 17 → 11, C 2/6 → 1/7, `REF_CORE` 6 → 5) are owed the same
treatment wherever `qol-21` published them.

*Renumber into your sequence or close it — the call is yours.*


---

## 2026-08-23-architecture-28 — INBOUND FROM THE FAMILY-ARCHITECTURE LANE: QoL lane's to renumber or close

*Filed as its own immediate commit, per the tightening landed today in
§9.5a — the batching window is the whole hazard, and it is the only part a
filer controls. Owner's file read first (§9.5b): only the residue is here.*

### MASTER SHIPPED CONFLICT MARKERS TWICE, AND NO GATE IS POINTED AT IT

`47544f1` committed `docs/backlog/qol.md` containing `<<<<<<< HEAD`,
`=======` and `>>>>>>> cc3d9ec`; `a1bb01e` then appended `qol-37` **around**
them rather than resolving them, so the markers survived a second landing.
Resolved in `c83ab62`, keeping all three blocks in order (`qol-36`, `qol-37`,
INBOUND) — **no content was lost either time**, which is exactly why nothing
noticed.

**Every gate was green over that file, throughout.** `docs_check` gates marked
code blocks; `backlog-index.sh` gates the index's freshness — and the index
even **rendered correctly**, because `## ` headings parse fine on either side of
a marker. Nothing in the tree is pointed at *"is this markdown structurally
intact"* (`docs/family-architecture.md` §5.4b).

**Asked for: one grep step in `tools/ci.sh`** — `^<<<<<<< `, `^=======$`,
`^>>>>>>> ` over the tracked tree, FAIL on any hit. It is a two-line step, it
has never been able to false-positive on this repository's prose, and it would
have caught both landings at the moment they were made.

*Renumber into your sequence or close it — the call is yours.*

---

## 2026-08-23-qol-38 — the marker gate I owed, a self-citation I created, and recovery by content

### The inbound: master shipped conflict markers twice, and both were mine

`47544f1` committed `<<<<<<<` / `=======` / `>>>>>>>` into `docs/backlog/qol.md`;
`a1bb01e` then appended `qol-37` **around** them rather than resolving them.
Nothing noticed, and the reason is the finding: **no content was lost either
time**, `docs_check` gates marked code blocks, `backlog-index.sh` gates index
freshness, and `## ` headings parse fine on **either side** of a marker.
Nothing was pointed at *"is this markdown structurally intact"*.

`tools/ci.sh` now carries one `git grep` over the **tracked** tree and fails on
any hit, naming file and line. Verified in both directions against a real
throwaway repo: a clean tree passes, a committed marker fails and is named. The
live tree is clean.

**The one false positive it can have is named rather than discovered:** a
Markdown **setext** underline of exactly seven `=` is legitimate and would trip
it. The tree has none — measured — and this repository writes `##`, so if it
ever fires that way the heading is what changes, not the gate.

### A self-citation I created inside the hour

Adding a self-test row naming `A15` made **`laws.sh` credit itself as A15's
gate** — the instrument that measures enforcement counting its own test data as
enforcement. That is the audit's self-selection defect, re-created by my own
fix, and it moved a law out of NO GATE for no reason at all.

**A fixture is not enforcement.** The self-test region is now stripped before
any attribution grep. Two rows pin it: a token that appears **only** in a
self-test does not gate, while one outside it still does.

### The amendment rows were unreadable exactly where the ranking points

An amendment's third column is its **status**, not a home, so the top-ranked row
printed `**new** (its RSS number is SUPERSEDED by 16)` where a location belongs.
Display now shows `docs/family-architecture.md §7.1a register — <status>`.
**The token path is deliberately untouched:** giving every amendment the literal
`§7.1a` home would credit *all* of them to any tool citing that section, which
is the over-crediting the boundary work exists to remove. A row asserts the
tokens stay `A15 amendment 15` with no `§`.

### Recovery by CONTENT, not by clock

The R-track lane measured my mtime-window rule wrong: **three `triad-build.*`
files landed within ninety seconds of one tenure's end** — other lanes'
gate-phase builds — and the file whose mtime matched was a **gate-phase
completion, not that tenure's last line**. `grep -l` for a symbol only that
build could have printed found **exactly one**.

The printed line and §9.5 now say: **recover by the printed path; failing that
by CONTENT; never by clock.**

### The instrument is outgrowing its own budget, and I have not fixed it

`laws.sh` was 54 s, then 1 m 23 s, and now exceeds **two minutes** — the tree
has grown to 343 laws and 18 tools, and attribution is a grep per (law × file).
I cached the stripped text per file and added a corpus short-circuit so a law
cited by nothing costs one grep instead of eighteen; it is still over budget.
**It needs the `--budget`/PARTIAL treatment `sites.sh` already has**, and until
it does, the re-rank runs in the background rather than in a foreground window.
Recorded as owed rather than left to be rediscovered.

**A coverage hole found on the way:** the cached fast path was **untested** —
the self-test never initialised the cache, which is why an ordering bug in it
(the corpus short-circuit running *before* identity attribution, silently
dropping `MEAS-60`/`OPS-46`'s script homes) passed 30 green rows. Three rows
now drive the cached path directly.

### Triad

`bash -n` clean. `laws.sh` **33 ok** (28 → 33), `triad.sh` **176 ok** (174 →
176), `ci.sh --verify-guards` **17 ok** (14 → 17). `docs_check` **91/91**. The
marker gate reports the live tree clean. No Lean executed.

---

## 2026-08-23-qol-39 — laws.sh was SPAWN-BOUND, so its runtime was other lanes' load

Ruled first because *a tool that prices enforcement must itself be priced*, and
**a two-minute audit instrument stops being run** — which is how audit
instruments die.

### Profiled before optimizing, and the profile refuted my first guess

Phase timings on the real script: `cache 1 s`, then **the ROWS loop is
everything**. But the same per-law work, measured over a pre-read file, came to
**13 s** — and three slices (rows 1-30, 150-179, 300-329) were **uniform at
~1.15 s each**, so no subset of laws is pathological.

The gap is **process spawns**: ~8000 of them, at four-to-six per law, and
**spawn latency scales with machine load**. That is why the same instrument
measured 54 s, then 1 m 23 s, then 1 m 55 s, then past two minutes as other
lanes' builds came and went. **Its runtime was a function of somebody else's
work** — §5.4a's own subject, pointed at the instrument that audits the
instruments.

### The fix follows the profile, not a hunch

* `home_tokens`: three `grep -oE | sort -u` pipelines → **one awk**.
* `ledger_citations`: one recursive grep **per token over fifteen files** → one
  awk over a corpus concatenated once, for all of a law's tokens together.
* `$(basename "$f")` inside the per-file loop → `${f##*/}`, no spawn.

**62 s, from over 120 s — and the numbers are byte-identical** (231 cited, 118
NO GATE, 1 ungateable). That equality is the check that matters: an
optimization that changes a count has changed the instrument, not its cost.

**The boundary survived, and it has its own row.** Counting with `index()`
would have been faster still and would have dropped the whole-token rule —
exactly how `§9` came to match `§9.5`. The awk escapes and anchors each token,
and a self-test asserts `§9` counts **0** against a ledger that says `§9.5`
twice, while `§9.5` counts **2**.

### And the budget, because 62 s is not 6 s

`--budget` (default 120 s) with progress every 50 laws, and past it the run
stops and says so:

```
  PARTIAL — stopped after 5s at law 24.  Every count below is a FLOOR, not a total.
            Raise --budget and re-run before quoting any of it.
```

The subshell writes the verdict to a **file** rather than a variable — the
same reason `triad.sh`'s watchdog publishes its pid instead of exporting it.

### Triad

`bash -n` clean. `--self-test`: **35 ok, 0 failed** (33 → 35). Full run 62 s
with unchanged numbers; `--budget 5` stops at law 24 and declares its counts
floors. No Lean executed.

---

## 2026-08-23-qol-40 — `laws.sh --gate-set`: §5.4b made checkable, and `.sv` has no gate

§5.4b's incident is the one where **every gate was green while the file said
the opposite of the truth** — four gates, four elsewheres, and the rotted claim
lived in a `.lean` **comment** that none of them pointed at. This enumerates
the pointers.

### The honesty clause is the first thing it prints

> **Enumeration reads DECLARATIONS.** A gate whose target is computed at
> runtime is listed **UNRESOLVED**, never guessed — a guessed pointer is worse
> than a missing one, because it makes a claim look **covered**. And §5.4b's
> own rule applies to this mode: **a gate set is audited by ENUMERATION, never
> by execution**, so nothing here runs a gate.

Live: **16 gates declared, 2 UNRESOLVED** — `conflict-markers` and
`tool-self-tests`, both shell functions whose targets really are computed. They
are named as unresolved rather than credited.

### The gate's own words are half the enumeration

A step declared `python3 tools/docs_check.py` names only the **script**; its
**scope** is in that script's header — *"Scans README.md, AGENTS.md, and
docs/\*\*/\*.md"*. Reading only the declaration left `.md` looking orphaned
while `docs_check` was pointed squarely at it. §5.4b says it plainly — *a gate
that documents its scope has already done half the enumeration* — so the mode
reads both, and the orphan list went from five kinds to one.

### The one orphan is real, and it is not a small one

```
  ORPHAN KINDS — present in the tree, named by NO gate's declared pointer:
    .sv        no declared pointer names it
```

Verified rather than reported: **`harness/sv_round_trip.py` exists and appears
in `tools/ci.sh` zero times**, against **18 `.sv` files** in the tree. (The four
`sv/` matches in ci.sh are `harness/sv/diff_test.py` — a different thing.) That
corroborates the audit's own note that some harnesses are never invoked, and it
is exactly the §5.4b shape: **a kind nobody has pointed a gate at, in a
neighbourhood that is otherwise green.**

`MEAS-68` rows are flagged `WEAKEST(MEAS-68)` from the declaration's own words
— an expected-to-error gate's verdict is **invariant under everything else the
artifact says**.

### A defect that made every kind look orphaned

The first run reported **16/16 UNRESOLVED** and five orphan kinds. `gate_rows`
emitted five tab-separated fields with two empty placeholders — and **TAB is
whitespace, so bash collapses consecutive tabs into one delimiter**, landing the
declaration in the wrong variable. A padding field you cannot see is a padding
field that is not there. Three fields now.

### Triad

`bash -n` clean. `--self-test`: **43 ok, 0 failed** (35 → 43), calibrated on
§5.4b's own table — gates read from declarations, a declared script as a
pointer, the gate's own words extending it, an `EXPECTED TO ERROR` row flagged
weakest while an ordinary one is not, a runtime target left UNRESOLVED rather
than guessed, and the incident's `.lean`-alongside-`.md` shape. No Lean
executed.

---

## 2026-08-23-qol-41 — two tools that disagreed, and stamps that read the wrong repo

### The glob disagreement, resolved by deleting the second parser

`check.sh` read `lakefile.toml` and called a repo-root `.lean` **scratch** —
correct, since `Examples.+` matches no root module and the `LeanModels` lib's
root is `LeanModels.lean` itself. `triad.sh` hard-coded `LeanModels/*|Examples/*`
and warned **"UNSTAGED LEAN UNDER A LAKE GLOB"** about the same file. It warned
rather than refused, so it was safe today — and the R-track lane's words are
the reason it still had to go: *two protocol tools disagreeing about the same
file eventually gets trusted in the wrong direction.*

`tools/lakeinfo.sh` now holds the reader, **sourced by both** — not a second
parser, which is the defect `dupes.sh` counts. Live: `check.sh` says `CASE
scratch` and `triad.sh` warns **zero** times about the same file.

**The fix had to go one level deeper than the classifier.** Rewiring
`classify_path` was not enough: the warning is emitted by
`lean_glob_offenders`, which asked *"is this not-docs?"* — and a repo-root
`.lean` is `spine`, which is not-docs. **The warning names a lake glob, so the
lakefile is what decides it.** Three rows pin it: a repo-root `.lean` is not an
offender, both tools agree it is `scratch`, and a real library file still is
one.

### Stamps must name their repo

`cd X && nohup Y > log 2>&1 &` backgrounds the **entire conjunction**, so the
R-track lane's follow-up `git write-tree` ran in the **wrong repository** and
printed another repo's HEAD as a MISMATCH. **With coincidentally-equal trees
the same bug yields a FALSE MATCH — a lane confirming a stamp it never
checked.** And in agent threads cwd does not persist between calls at all.

Every live `git` in `triad.sh`'s classify and stamp paths now carries
`git -C "$CLONE"`. The self-test **runs the stamp from `/`** and asserts it
still reads the repo it was told about, and that the result is not the outer
repo's HEAD — the false-match direction, checked rather than assumed.

I hit this same shape myself an hour earlier: a `cd … && nohup … &` line left
its follow-up `grep` running in the session's cwd, which is why it reported
`tools/triad.sh: No such file or directory` in a repo that plainly has one.

### Triad

`bash -n` clean. `check.sh` **87 ok** (the row that read `lake_lib_roots` now
passes the clone **explicitly** — the shared reader takes its root as an
argument, which is the same rule as the stamps). `triad.sh` **181 ok** (176 →
181). `laws.sh` 43 ok. No Lean executed.

## 2026-08-23-qol-42 — the SV round-trip gate joins CI, and qol-40's orphan was half instrument

`laws.sh --gate-set` reported `.sv` as an orphan kind (qol-40). Closing it
turned up two findings that point opposite ways, and both belong here.

### The gate really was not in CI

`harness/sv_round_trip.py` appears in the committed `tools/ci.sh` **zero
times** — measured against HEAD, not inferred. It is host-safe: it re-runs
`extractors/sv/extract.py` over every committed
`Examples/system-verilog/**/*.sv.json` inside a scratch mirror and compares
bytes. No simulator, no network, no Lean. It takes **no argument** (`REPO` and
the envelope root come from the script's own location), so wiring it needed no
path. It is now a full `step`, called unconditionally: a tracked file is not
optional.

**The interpreter is part of the gate.** Measured before wiring, on a host
without pyslang: all 18 live envelopes come back `REFUSE extractor-failed:
ModuleNotFoundError: No module named 'pyslang'`. That is a red reporting an
**absent package as though it were envelope drift** — the one distinction this
gate exists to make. So the step chooses its interpreter **by capability**
(which `python3.12`/`python3` can actually `import pyslang`), never by name:

* a capable interpreter → the gate runs, here and on a runner;
* none, off CI → a named SKIP, because pyslang is **not tracked** — the same
  discriminator `maybe` applies to an absent simulator;
* none, on a GitHub runner → **FAIL**, because `.github/workflows/ci.yml`
  installs it there, so a runner that cannot import it has a broken install
  and skipping would retire the gate exactly where it is the only reader.

### ...but "no gate names `.sv`" was my own instrument under-reading

`gate_rows` anchored its match at **column 0**. Every host-gated gate is
declared *inside a function or an `if`*, so it is indented, so the enumeration
never saw it. Measured: **16 gates before, 44 after** — the fix recovered
`lake-build` (an auditor reading that list would have concluded CI does not
gate the build at all), 27 simulator-gated spice/sv/rv rows, and the new one.

The counterfactual is the honest test, so it was run: **new `laws.sh` against
the OLD `ci.sh` reports 43 gates and NO orphan kinds.** `sv-harness` and
`sv2-harness` were already pointed at `.sv` and my anchor hid them. So qol-40's
finding was **half instrument artifact**, and this entry corrects it.

What survives the correction: those two rows are **simulator-gated** and SKIP
when neither `iverilog` nor `xrun` is on PATH, which is a stock runner. On CI
`.sv` had **no gate that runs**, and the round-trip gate is precisely the one
that can — so the wiring was worth doing for a reason narrower than the one
that prompted it. Leading whitespace is indentation, not evidence.

**A fixture is not enforcement**, applied to declarations: `--verify-guards`
drives these same functions with stubs, so that region is cut before matching.
It is cut inside `gate_rows` rather than in `enforcement_text`, whose keying is
the self-test spelling and whose citation counts are not this inch's to move.

### Left standing, named rather than fixed

`gate_rows` enumerates a **declaration**, so a gate wrapped in a function that
nothing ever calls would still be listed. "A declaration is not a call" is the
next cousin of the fixture rule; here the call site is pinned by a
`--verify-guards` row asserting `^sv_round_trip_step$` instead.

### Triad

`bash -n` clean. `ci.sh --verify-guards` **26 ok** (17 → 26), `laws.sh` **45
ok** (43 → 45), `triad.sh` 181 ok, `check.sh` 87 ok, `docs_check` 5 ok. No Lean
executed.

## 2026-08-23-qol-43 — arming a byte-comparing gate arms the pins it does not have

The SV lane's finding, one line to stop the bleeding. Verified rather than
taken on faith: `.github/workflows/ci.yml:29` installed pyslang **unpinned**,
while `extractors/sv/extract.py` sets
`FRONTEND = {"name": "pyslang", "version": pyslang.__version__}` and writes it
into every envelope — **all 21 committed envelopes carry `"version":
"11.0.0"`** inside the exact bytes `sv_round_trip.py` compares (measured:
`21` of `21`). The extractor's own docstring already says it: *"same input
bytes (and same pyslang version) => same output bytes."*

So the next pyslang release turns **every PR red with 21 DIVERGEs unrelated to
anyone's change** — and it does so *because* qol-42 armed the gate. Pinned to
`pyslang==11.0.0` on both arms of the `||`, marked **TEMPORARY — remove when
extract.py stamps the family (SV Landing A regenerates the envelopes)**. SV
owns the real fix. YAML re-parsed: 7 steps.

**And the same defect one level down, in a line I wrote twenty minutes
earlier.** The SKIP branch's hint said `pip install pyslang` — unpinned. A
developer following it after the next release would install 11.0.1, run the
gate, get 21 DIVERGEs, and conclude the envelopes had drifted: exactly the
misreading the capability check exists to prevent. Pinned too. A hint is an
instruction, and an instruction that reproduces the defect is the defect.

Left standing, named: `docs/sv-charter.md:138` records that a clean venv yields
pyslang 11.0.0. That is a **dated measurement**, not an instruction, and it is
the SV lane's document — but it will quietly stop being true.

### For the register — a new defect family

> **An unconditional byte-comparing gate inherits every unpinned input of the
> artifact it compares; arming the gate arms the pins it does not have.**

The gate was harmless while it sat unwired: an unpinned input costs nothing
until something compares against it on every PR. The family is not "pin your
dependencies" — it is that **wiring a comparison changes the blast radius of
inputs nobody edited**, so the pin audit belongs to the *arming* commit, not
to the gate's author.

### Triad

`bash -n` clean, `ci.sh --verify-guards` 26 ok, YAML parses. No Lean executed.

## 2026-08-23-qol-44 — a flag written last spun forever, in eleven tools

The Go lane's defect, reproduced before it was fixed:
`timeout 3 bash tools/triad.sh --gates` returns **124 with zero bytes of
output**. Three tolerant parts compose into a hang — `${2:-}` accepts the
missing value, `shift 2` then fails because one argument is left (and there is
no `set -e`), and `while [ $# -gt 0 ]` re-enters on the **same** argument. No
output, no lock taken, nothing to distinguish it from waiting in the queue, so
the natural response is to wait longer. It cost Go **31 minutes over two
runs**.

**It was not one arm, it was the shape.** Eleven of this lane's tools carried
it: triad 8, sites 4, check 3, laws 3, substrate 2, analogues 2, dupes 2,
backlog-index 2, new-proof 1, editions 1 — **28 flags**, every one of which
spins if written last. Fixing only the reported one would have left the next
lane to re-pay the same 31 minutes for `laws.sh --budget`.

One guard, in `tools/argv.sh`, sourced by all eleven — the same "one source"
rule that ended the check.sh/triad.sh glob disagreement. It **refuses**; it
never defaults, because the near-miss is worse than the spin.

### The near-miss, and the line that ends it

A run that merely LOST its `--gates` value would **complete and report green
on the default floor** — less coverage than the lane believes it bought, with
nothing in the log to say so. The guard closes the path that produced it; it
should not take a guard for a log to be honest about its own scope. A tenure
now names both halves at open:

```
[20:04:56] gates: python3 tools/docs_check.py; python3 harness/diff_test.py; python3 tools/docs_check.py
[20:04:56] gates asked by the lane: python3 tools/docs_check.py (--gates: ADDS to the floor)
```

Composed by `gates_planned`, which calls **the same `gates_compose`** the gate
phase calls, against a `DEFAULT_FLOOR` constant that used to be a literal
inside the phase — because an announcement that can drift from the phase lies
in the reassuring direction. Six rows pin the composition and one asserts the
announced set equals the phase's own composer's output.

Visible in that transcript, and pre-existing: an additive `--gates` naming a
floor gate lists it **twice**. `gates_compose` is deliberately additive and a
row already covers it; what is new is that the lane can now SEE it. Named
rather than changed — it is the SV/Ada lanes' call whether a de-dupe would
silently shrink anything.

### The gate, discovery-based

`ci.sh` gains `argv-guards`: for every value-taking flag **found by reading
the tools**, the probe must TERMINATE (not 124 — the spin) and must NOT
SUCCEED (not 0 — the near-miss). A list would have to be maintained by the
same attention that wrote the unguarded arm. Live: **28 flags probed, 27
refused by name, 0 tolerant** (new-proof's `--out` refuses one step earlier,
at its positional check).

**Two under-reads in my own gate, both the rules I had just written.** The
first discovery pass matched `--flag).*shift 2` on ONE line and so missed
`sites.sh --channel`, whose arm spans two lines — the same column-0 anchoring
that had `--gate-set` reporting 16 gates where the file declares 44, repeated
within the hour. An arm runs to its `;;`. The second pass then discovered
`--flag` from the two fixture scripts heredoc-ed into `ci.sh` itself and
probed `ci.sh --flag`: **a fixture is not a tool**, the same cut `gate_rows`
already makes.

### The rebase law (Go's third item)

`--classify` said, for `docs/*.lean|harness/*.lean|tools/*.lean`, only that
running it is Lean execution (A11). Two things were wrong: the list was three
**hard-coded prefixes** — the hard-coding `lakeinfo.sh` exists to end, so a
`.lean` under `probes/` or at the repo root got no note at all — and it never
said the consequence. Now asked of the lakefile, and it says both halves:

> `'probes/x.lean'` is OUTSIDE ALL lean_lib ROOTS (LeanModels Main) —
> `lake build` never compiles it, so a rebase touching only it owes no
> re-gate; but RUNNING it is still Lean execution (A11): pass --gates

Classification itself is unchanged: such a file stays `spine` unless it is
under `docs/`, because probes ARE run by gates. The note explains; it does not
downgrade. Four rows, including the direction that matters — a library `.lean`
is **not** excused.

### Triad

`bash -n` clean on all 13 tools. `triad.sh` **196 ok** (181 → 196),
`ci.sh --verify-guards` **32 ok** (26 → 32), and check 87, laws 45, sites 44,
diagnose 51, backlog-index 34, new-proof 31, analogues 28, substrate 25,
editions 12, dupes 10, a6-guard 8 — all unchanged and green after the
mechanical rewrite. The enqueue line was confirmed end-to-end on an **isolated
lock and queue** (`LS_LOCK`/`LS_QUEUE` in the scratchpad, `--dry-run`, a
refusing `lake` stub on PATH): the machine-wide lock was held by another lane
and was never touched. No Lean executed.

## 2026-08-23-qol-45 — the shape set's fourth member, and a log that says whose it is

Two items from the C successor's recovery.

### ANNOTATE: a position no threshold could have found

`runIndetRaw : … Halt …` is a **type annotation**. It names the type and no
constructor, so every channel this tool had — all of which grep `\.$CTOR` —
was structurally blind to it. The successor's census counted value
constructors and destructures, called the change priced, and **red a tenure**
on the signature that survived. A bound a whole syntactic position can walk
through is not a bound, and the failure is one of KIND: no threshold on the
old channels would have caught it, because it was never a smaller count.

> A CONSTRUCTOR change is bounded by DESTRUCTURE. A change to the TYPE ITSELF
> is bounded by DESTRUCTURE + ANNOTATE: renaming or deleting a type breaks
> every signature that names it, none of which names a constructor.

Live on this tree, `sites.sh Halt unsupported`, full scan, no PARTIAL:

```
DESTRUCTURE  13 site(s)
CONSTRUCT    18 site(s)
ANNOTATE     20 site(s) name `Halt` in a TYPE POSITION, 20 of them naming
             NO constructor — invisible to every count above
```

**All 20.** The type has more annotation sites than destructure sites, and the
old census could see none of them — the priced bound understated the
type-change surface by twenty sites, which is the incident, reproduced as a
number.

The test is positional like the rest of the tool: the type stands to the RIGHT
of a `:`, with `:=` and `::` removed first, so a body-local `(x : Halt)`
ascription counts and a cons does not. One discrimination had to be learned
mid-landing: **a leading dot and a qualifier are different dots.** Excluding
every preceding `.` rejected `LeanModels.C.Halt` — the qualified spelling this
tool's own channel list already treats as the type — while allowing every dot
would have accepted `.Halt`, an anonymous constructor. What precedes the dot
decides. Thirteen rows, including `onHalt` (a field name colliding on the
WRONG side of the colon) and the three shapes that must not count.

**And I made it twice as slow before I made it fast.** The first cut called
the comment-stripper a second time per file: the live run went **PARTIAL at
file 5040 of 9825** where the old one reached the end. The stripper is the
expensive part and does not depend on the pattern, so the second regex now
rides the first traversal. Measured, same 45s budget, same tree: baseline
**3626** files, two channels **3732**. The channel is free.

### A build log must say whose it is

`triad-build.*` held ONLY lake output — no ticket, no lane, no branch, no
tree. The C successor lost its transcript, grepped **68 of them** for its lane
tag, and **matched nothing**. Every log was still on disk; not one could be
attributed. `build_log_pointer` already recovers a log by path and, failing
that, by content — neither helps when the content itself is anonymous.

Each attempt now stamps one line first:

```
triad.sh ticket=1787514607204600000-87469-ctwin lane=ctwin branch=master
tree=a0ca12e46087 head=95849db dir=/Users/ahle/repos/lean-qol attempt=1 at=…
```

**Per attempt, because the redirect truncates**: a header written once at open
is erased by attempt 1 and again by the resource-kill retry. Header with `>`,
lake with `>>`, so one-attempt-per-log is exactly as before.

**A header that rides in the file the failure reports COUNT must be inert**,
and that is checked rather than reasoned about: the same red log with and
without it yields byte-identical `error lines`, `failed modules`, and axiom
ledger verdicts. Also asserted: no hostname. Confirmed end-to-end with a
stubbed `lake` on an isolated lock and queue — the header is line 1 of a real
`BUILD_LOG`, `grep -l 'lane=ctwin'` now finds it.

### Triad

`bash -n` clean. `sites.sh` **57 ok** (44 → 57), `triad.sh` **207 ok** (196 →
207), `ci.sh --verify-guards` 32 ok. No Lean executed: the end-to-end run used
a `lake` stub and `--gates-only python3 tools/docs_check.py`, on `LS_LOCK`/
`LS_QUEUE` in the scratchpad; the machine-wide lock was never touched.

## 2026-08-23-qol-46 — the floor grows a gate, and a tenure says what it could have been

Two floor-policy items, taken together because they are the same surface.

### refusal_census joins the non-docs floor (by ruling)

`python3 harness/refusal_census.py --whitelist --no-build` is now in the floor
for every non-docs class. Its §5.2 invariants — every interpreter refusal
carries a class, no row is undefined — used to fire only when a lane happened
to pass `--gates`, and **an unexercised gate is not a gate, it is a claim**.
It is the no-UB claim's only external check.

Doc-first: triad.sh's §7 surface comment now states the floor by class, and
`docs/family-architecture.md` §7.1a enumerated its members (`docs_check` /
`diff_test`) — that sentence was wrong the moment the floor changed, so it
landed in the same commit. **Model and code together.**

**`--no-build` is not decoration in that line.** The tenure prebuilds
`leanmodels-run` in the gate phase; a gate that builds turns a build defect
into a gate failure, which is the misattribution the gate-phase build exists
to prevent. The census honours `LS_RUNNER_PREBUILT` exactly as `diff_test` and
`script_corpus` do, so belt and suspenders are both present.

**Two defects found while wiring it, neither in the ruling:**

* `gate_floor` carried its **own second copy** of the floor list, so the
  classified path and the unclassified path could have run different gates
  with nothing saying so. Both now read `DEFAULT_FLOOR`. A floor that has to
  be edited twice gets edited once.
* `gate_runner_targets` matched `diff_test|script_corpus|"lake exe"`, and the
  census names its runner through its own `--runner` default. It would have
  worked **by accident** in the floor (which also contains `diff_test`) and
  failed under `--gates-only`, where a lane would have reached `--no-build`
  with nothing built and read a missing runner as a census failure.

Five existing rows asserted the OLD floor and had to be updated — which is
what a floor change should feel like. One of them was counting `--no-build`
across the whole floor and started reading 2; it now counts on **diff_test's
own segment**, since the point of that row is the flag this function adds.

### The class advisory: (b), and why not (a)

`--classify` is opt-in, so a plain `--lane X` on a docs-only diff queues a
FULL tenure. Two options were on the table; the choice is not close.

**(a) classify by default, `--no-classify` to opt out — rejected.**
Classification NARROWS the build, so this makes **narrowing the default**:
every lane's coverage would depend on the classifier being right without
anyone having asked. That is the exact reading the `--gates` ruling rejected —
"it takes the reading that cannot silently shrink a gate set". It also turns
working runs into refusals: `--classify` dies without a merge target, refuses
on unstaged Lean under a lake glob, and CONTRADICTS `--foreign` by design.
Three hard stops imposed on invocations that asked for none of them.

**(b) chosen.** One line at enqueue, always, including when it cannot tell:

```
class: this diff classifies DOCS against origin/master — a FULL tenure was
       queued anyway. --classify takes the floor, and a docs-only landing
       owes NO TENURE AT ALL
```

Behaviour is unchanged; the lane learns what it could have taken, in time to
act on the next one. Silence would be ambiguous between "right-sized" and
"the probe did not run", so the line is unconditional.

**It runs in a subshell, and that is the load-bearing part.** `classify_list`
sets `CLASS_RANK`, `CLASS_TIERS` and `BUILD_TARGETS`; an advisory that leaked
those would narrow the very build it only describes. `$( … )` cannot leak a
variable — the trap this lane has been bitten by three times is here exactly
the right tool. A row sets `BUILD_TARGETS=SENTINEL` and asserts it survives.

**A vacuous pass, caught.** That sentinel row and its neighbour passed on the
first run for the wrong reason: `class_hint` was defined AFTER the self-test
block, so the call was `command not found` and `BUILD_TARGETS` stayed
SENTINEL because nothing had run. Only the rows expecting OUTPUT failed
(rc 127), which is what exposed it. **A row that asserts a variable did not
change passes when the code never ran** — such a row needs a sibling that
asserts the code DID run, and here the docs/spine rows are that sibling.
Both definitions moved above the self-test.

An empty diff is never read as docs-only: it measured nothing, and the full
tenure is the safe reading — the same rule `--classify` already applies.
No merge target is an advisory line, never a refusal.

### Triad

`bash -n` clean. `triad.sh` **230 ok** (207 → 230), `ci.sh --verify-guards`
32 ok, sites 57 ok. Confirmed end-to-end on an isolated lock and queue with a
stubbed `lake`: both the floor line with its label and the advisory print, and
`--classify-only` reports the same floor — one spelling, two paths. The census
itself was NOT run here: it executes the model, which needs a tenure (A11).
Its flags were verified from `--help`, which runs nothing.

## 2026-08-23-qol-47 — increment greens, phase 1: a green may rest on a named green

The pyc lane withdrew a wasteful ticket and proved its increment's class by
hand (`git diff --name-only <green-sha> HEAD`, two docs files). Phase 1 makes
that mechanical, under the three rulings.

### The finding that shaped the design: nothing recorded greens

Only the lock and the queue persisted, both in `/tmp`, both ephemeral. "The
branch was green an hour ago" was a **memory**, and an increment cannot rest
on a memory. So the ledger is the feature and `--since` is a thin flag on it.

`.git/triad-greens`: untracked (it can never conflict — the INDEX.md scar),
inside the git dir (survives rebase and checkout), and **per working
directory** (`--git-dir`, not `--git-common-dir`) because a linked worktree
has its own `.lake` and the cache is part of what produced the green. A green
recorded elsewhere is not verifiable here, and its absence here is honest.
**Evidence does not travel by assumption.**

### A green certifies a TREE, not a commit

The stamp is `git write-tree` — the INDEX tree — plus HEAD, so a green can
certify content that is not any commit. Citability is exactly
`git write-tree == git rev-parse HEAD^{tree}` (verified: both `e24588c1` on a
clean tree here). A green whose index tree is not its commit's tree is
recorded `citable=no` and refused as a base: the sha would name something the
green did not certify.

### Five refusals, all before the ticket

Not a commit; **not an ancestor** — which is also what makes rebase safe,
since a rebase writes new shas so a green from before one can never be cited;
no recorded green ("a green is evidence, not a memory"); `citable=no`; and no
resolvable root. Plus an **empty increment**, which the branch-diff path
treats as "measured nothing" and falls back to a full build — but a lane that
asked to price an increment asked about something that does not exist, so it
is refused instead. And two contradictions: `--since` requires `--classify`
(not implied — implying a flag changes behaviour silently, and the precedent
here is `--foreign requires --gates`), and `--since` contradicts `--against`.

### Root-based classification, and what the run showed

Classification is taken against the chain **root**, never the named green.
Naming any recorded green is allowed; when the two differ the run says so:

```
INCREMENT: you named the green at 9f8e7d6; classifying against its ROOT a1b2c3d
           instead (§5.4a-i: against the root, never the parent — two
           increments priced against their predecessors can be tier A and
           tier B with neither build covering both)
```

**Two bugs the end-to-end run caught that the unit rows did not.** First,
`targets=` came out EMPTY for a full build, so the coverage line printed
`targets , recorded …` — a blank where the most important word belonged.
`sed 's/^$/all/'` does not fire on empty *input*: there is no line to match.
Second, and worse: an increment run whose build was **not** narrowed (a docs
class that keeps its tenure builds every default target) was recorded as
`depth=1` under an older root. **A full build is its own root, however it was
reached** — that test now comes first, and the merge bar is stated in terms of
what the root BUILT.

### The composed coverage line, live

```
COVERAGE (§5.4a-i): INCREMENT green.
  increment  ad64a3d..6992dfc  (1 file(s), class docs)
  on top of  the green at ad64a3d (class spine, targets all, recorded …)
  root       ad64a3d (FULL build)
  docs-only: NO Lean was elaborated, …
  This green is evidence about THE INCREMENT ON TOP OF THAT GREEN and nothing
  else. It is NOT evidence that the branch is green as a whole, and it inherits
  every limit of the green it rests on.
  MERGE BAR: SATISFIED — the chain root is a FULL green and this increment was
             classified against that root (§5.4a-i).
```

The clause is unconditional, including when the base was a full build: what it
guards against is the **reading**, not the base. A scoped root prints
`MERGE BAR: NOT SATISFIED` and says to take a full green.

### Triad

Doc-first: `docs/family-architecture.md` §5.4a-i and triad.sh's §7 surface
landed with the code. `triad.sh` **258 ok** (230 → 258), `--verify-guards`
32 ok, docs_check 91/91. Verified end-to-end on scratch repos with a stubbed
`lake` and isolated `LS_LOCK`/`LS_QUEUE`: a root green recorded, an increment
resolved against it, the chain written, and all three precondition refusals
fired. No Lean executed; the machine-wide lock was never touched.

## 2026-08-24-qol-48 — the stamp was watching the index while lake read the working tree

Four items; the third arrived mid-flight and went first, because it is the
enforcement layer the other two decorate.

### The integrity hole (wasm lane) — verified before it was fixed

`tree_stamp` was `git write-tree`, which hashes the **index**. `lake` compiles
the **working tree**. So an uncommitted, unstaged edit between enqueue and
acquire moved exactly the files lean reads while leaving the stamp identical:
the guard passed, the tenure ran, and the green certified a tree the gate
never saw. The Ada wrong-tree hazard, mechanized into the tool that exists to
prevent it.

**Measured in this clone while writing the fix** — index `2fd6962…`, working
tree `112a516…`, because triad.sh itself was edited and unstaged. The guard
had been comparing the wrong one, demonstrable on the spot.

The fix hashes the working tree through a **temporary** `GIT_INDEX_FILE`, so
the lane's real staging area is never touched. `add -A` includes untracked
files (a new `.lean` is exactly what must not slip in) and honours
`.gitignore` (so `.lake` churn cannot defeat the stamp — verified: 0 `.lake/`
entries). Cost: **0.31 s cold against 0.015 s**, twice per tenure.

**The index-only case is ACCEPTED, deliberately.** Content staged but absent
from the working tree will not be elaborated, so it is not part of what the
tenure certifies. The old stamp refused it — a false alarm in the opposite
direction. Both directions now have a row.

**Old tickets are not stranded.** Eight tenures were live. A stamp now carries
`v2`; a `v1` stamp against a `v2` one is `unversioned`, which **accepts and
logs** rather than refusing — they answer two different questions, and an
answer to one is not evidence about the other. Refusing would have killed a
full queue for a defect that was the tool's.

**The same blindness, one level down, in my own work from yesterday.**
`record_green` also called `git write-tree`, so a green taken with an unstaged
edit recorded the index's hash and could be judged *citable* while the
elaborated content was something else. Fixed at the same time, one source.

### Delta vs master at enqueue (Ada)

After `tree at enqueue:`, one pure-git line: `delta vs master: 1 file(s),
0 .lean — DOCS-ONLY`. A title is a claim about intent; the tree is what was
elaborated, and when they disagree the green is about the tree.

**One deviation from the brief, and it is the incident one level down.**
`0 .lean` is **not** DOCS-ONLY: `lakefile.toml`, `lean-toolchain` and
`lake-manifest.json` carry no `.lean` and invalidate the whole graph. Labelling
those DOCS-ONLY would have reproduced exactly the tree/label mismatch the line
exists to expose. The label is asked of `classify_path`, which already answers
it, and prints `— NOT docs-only (lakefile.toml)` instead. A row pins that.

**The absence family, three distinct members**, none of which may print like a
measurement: `n/a (foreign tree)` — refused before trying, since a foreign
checkout's `origin/master` is a different project's master; `n/a (no
github/master or origin/master in this clone)`; and `n/a (no merge base …
unrelated histories)`. Against `0 files (HEAD is at origin/master)`, which is
a measurement.

### The heading guard (analog founding) — extended, not duplicated

This was **half-built**: undated headings already sorted last and were counted
*inside the generated file* — a place the lane that wrote the heading never
looks. Measured across the tree: **18 undated, 8 malformed, 7 files.**

The discriminator is the token count before the em dash: **an id is ONE
token.** `G1 — title` is a real entry under an older scheme (undated: warn,
never fail, or `--strict` could never be adopted while Go's `G1`…`G18` exist).
`INBOUND FROM THE SOFTFLOAT LANE — …` is five tokens and yields the id
`INBOUND` — junk, and that is what `--strict` (exit 3) fails on. Warnings name
file, line and heading on stderr, on every generating mode.

**Two of the eight were mine**, now conformed to
`## 2026-08-23-qol-inbound-N — …` — **which was itself wrong, and §9.5a says
so**: an inbound entry carries a **SENDER-namespace** id so that nothing is
minted in the OWNER's sequence, and I minted two in mine. Re-spelled at
`2026-08-24-qol-51` to the architecture lane's own ids. The other six are one
per lane file, and
§9.5 makes a lane file appendable only by its own lane — so `--strict` is not
wired into ci.sh yet. That is the coordinator's call, and it is one line.

### The merge-target fallback (wasm fork)

`{github,origin}/master` was hard-coded, so a fork whose default branch is
named otherwise fell back to a full tenure — **conservatively, and therefore
silently, which is how a heuristic stays broken.** It now asks the remote
which branch is its head (`refs/remotes/<remote>/HEAD`) instead of guessing a
name. Order is still a preference, not an assumption.

### Triad

`triad.sh` **283 ok** (258 → 283), `backlog-index.sh` **47 ok** (34 → 47), and
check 87, laws 45, sites 57, diagnose 51, new-proof 31, analogues 28,
substrate 25, editions 12, dupes 10, a6-guard 8 — every tool that sources
`argv.sh` re-run green, and `ci.sh --verify-guards` **32 ok** including the
argv one-source gate. Fixture repos only: the live queue was verified
untouched (8 tickets, sv holding the lock) and every run used a stubbed `lake`
with `LS_LOCK`/`LS_QUEUE` in the scratchpad. No Lean executed.

## 2026-08-24-qol-49 — the merge left the model describing a guard that no longer exists

`22ed755` merged as `b98b4d0`. The merge is clean and green on master —
triad **283 ok**, backlog-index **47 ok**, `--verify-guards` **32 ok**,
docs_check 91/91 — and the two commits either side of it (`4b8585e`,
`17c8da1`) are **docs-only**: the architecture lane REGISTERED the stamp
finding in the same hours the tools lane FIXED it. No code conflict.

**But a docs-only neighbour is exactly how a model goes stale.** Four
present-tense claims survived the merge describing a guard that no longer
exists:

* `docs/family-architecture.md` §5.4a-i — **mine**, written yesterday: "the
  tenure stamp is `git write-tree` — the INDEX tree", and citability defined
  as the index tree matching HEAD's. My own fix falsified my own paragraph.
* §7.2's registration — "`tree_stamp` **is** `git write-tree`… fix dispatched
  to the tools lane as priority". The dispatch had already landed.
* §7.2's A6 gate description — "`tools/triad.sh` **now** stamps the index's
  tree".
* `docs/law-index.md` **OPS-78** — "the enqueue stamp hashes the INDEX; `lake`
  builds the WORKING TREE", pointing at `tools/triad.sh`.

Repaired surgically, preserving the architecture lane's analysis intact — the
reasoning is the register's value and none of it was wrong. Only the tense and
the status changed, plus a **RESOLVED** paragraph recording the two
consequences a future reader needs: the index-only acceptance, and stamp
versioning's accept-and-log.

**OPS-78 was restated as a LAW rather than a symptom.** "The enqueue stamp
hashes the INDEX" is an observation with a shelf life; the durable rule is
**a guard must hash the object the BUILD reads, never the one beside it** —
with the incident kept parenthetically so the row stays traceable.

The general shape, which is worth more than this instance: **when a finding
and its fix land from different lanes in the same window, the register
describes the defect in the present tense and the code has already moved.**
Neither lane is wrong and neither merge is dirty — the divergence is created
by the ORDER, and it survives precisely because both halves are green. Model
and code land together; when they land from two lanes, someone owes the
reconciliation at the merge.

### Triad

Docs only, no tool changed. laws 45 ok, docs_check 91/91, and the suite above
re-run on merged master. No Lean executed.

## 2026-08-24-qol-50 — nothing checked whether a ticket's base had ever been green

The pyc lane spent **116 minutes** of the machine-wide tenure (4852s queued,
2083s building) rediscovering a defect that was **already fixed on master
three minutes into its own build**. Its base was red for a full build when
committed, and nothing checked whether master had moved past it — least of all
during a queue wait hours deep, which is exactly when the fix lands.

### The line, at enqueue and again at acquire

```
delta vs master: 0 files (HEAD is at origin/master)
base: BASE STALE: 1 commit(s) behind origin/master tip d36344d
      (this ticket branches from 7113979) — consider rebasing before it runs
```

Those two lines are from the same run, and their disagreement **is** the
failure mode: the LOCAL tracking ref says "I am at master" while the remote
says master moved. Only a fetch can tell them apart.

Repeated at **acquire** as well, per the option in the brief — the enqueue
line is read by whoever typed the command, but the acquire line lands in the
log beside the verdict, and it is a *fresh* fetch, because a cached answer
from four hours ago is the very thing being warned about.

**WARN, NEVER REFUSE.** A pinned base is legitimate — SV declined a rebase the
same day for tree-certification reasons — so a guard that refused would have
been wrong about that lane while being right about pyc. A wrong warning costs
a line; a wrong refusal costs a tenure.

### The fetch must not move the lane's own refs

Measured while writing this: `git fetch origin master:refs/triad/tip`
**advances `origin/master`**, because git updates remote-tracking refs
*opportunistically* for any fetched ref that maps to one. Fetching **by URL**
has no configured mapping and updates nothing. A diagnostic must not move the
state the lane is about to be judged against. Bounded at 25s,
`GIT_TERMINAL_PROMPT=0`, ssh in batch mode: an enqueue must never block on a
network hang or an auth prompt.

**The absence family, four members, none reading like "at the tip":** foreign
tree, no merge target, unreachable remote, unrelated histories. And A13 gets
its own clause — a seeded clone's origin can be a local bundle whose tip is
days behind github's, which would report a stale base as current. The check
still runs; the line says `[A13: 'origin' is a LOCAL path — its tip may not be
github's]`.

### The one refusal, and why it may refuse

`stamp_version_guard` refuses a **NEW** enqueue from a worktree whose
triad.sh predates master's `STAMP_VERSION` — the leantier shape. The
distinction is the whole license: **accept-and-log is for tickets already in
flight; a new one is not one of them.** It fires before any ticket exists
(verified: 0 tickets created by a refused run), it is local once the tip is
fetched, and **an absent answer is never a refusal** — not knowing master's
version is not evidence that ours is old.

### The subshell trap, fourth encounter

The first cut returned the sha on stdout and the REASON in a global. Every
caller uses `$( … )`, so every caller read an empty reason and printed
`n/a ()`. **A subshell cannot set a parent's variable** — so the answer is now
carried the only way that survives one: **in the value**, with a leading `!`
marking a reason. The cache had the same disease and is now a file, the way
`laws.sh --budget` writes its PARTIAL verdict to one.

Also caught by a failing row: `git init --bare` points HEAD at
`refs/heads/main`, so a fixture cloning a repo whose only branch is `master`
checks out **nothing** — no HEAD, no merge-base, and six rows silently
measured the "unrelated histories" path instead of the ones they named.

### Triad

`triad.sh` **299 ok** (283 → 299), `ci.sh --verify-guards` 32 ok, and every
tool sourcing `argv.sh` re-run green. Fixture repos with a real local upstream
that moves mid-test; the live queue was verified untouched (6 tickets, lock
held) and every run used a stubbed `lake` with `LS_LOCK`/`LS_QUEUE` in the
scratchpad. No Lean executed.

## 2026-08-24-qol-51 — the id goes first, INBOUND becomes a title prefix

The generator side of §9.5a's recorded resolution. Arch found the collision
and routed it here rather than re-spelling six other lanes' headings —
**a convention in a charter can be a defect in a tool** — and recommended:
*the id goes FIRST, `INBOUND` moves into the TITLE, and the generator classes
on the title prefix rather than the id token.* Implemented as recorded.

### Old-valid is the load-bearing half

The acceptance asked for `--strict` to **pass** on a mixed tree, and it could
not have: the old INBOUND spelling was `malformed`, which fails. So the guard
gains a fourth verdict. **These headings are malformed BECAUSE THE CHARTER
TOLD FILERS TO WRITE THEM THAT WAY** — a shape the rules once required cannot
become a failure the day a new rule lands. `old-valid` warns, names the new
shape, and never fails.

The discrimination is narrow on purpose: a multi-word heading beginning with
`INBOUND` is the known prior convention; **any other** multi-word heading is
still junk. Live tree, before and after:

```
9 malformed  ->  3 malformed (the SPEC COVERAGE family)
                 6 old-valid (INBOUND, warn only)
--strict: exit 3, and now for one reason only
```

### The class survives the move

`rows` gains a fifth field and the page a `class` column. The class is read
from the **title prefix**; the id token is still honoured so the six headings
awaiting re-spelling keep their class while their owners re-spell them. That
is the whole resolution: `INBOUND` could not be both the class and the id, and
now it is only the class.

### And I had got my own two wrong

Conforming my two inbound entries at `2026-08-23-qol-49`, I minted
`2026-08-23-qol-inbound-1/2` — **ids in MY OWN sequence, for entries the
architecture lane sent me.** §9.5a exists to prevent exactly that: an inbound
entry carries a **SENDER-namespace** id so nothing is minted in the owner's
sequence. Re-spelled to `2026-08-23-architecture-27/28`, which were already
sitting in the body text where I had left them. The prose in qol-49 that
described the wrong spelling is corrected in place rather than left standing.

They are now the in-tree exemplar of the resolved shape:

```
## 2026-08-23-architecture-27 — INBOUND FROM THE FAMILY-ARCHITECTURE LANE: QoL lane's to renumber or close
```

### What the charter still owes

The generator now accepts the resolved shape; **§9.5a still describes the old
one.** Model-matches-code at the convention level means the charter wording
lands in the same window — arch owns that text, and the exact amendment is in
the report to the coordinator so it can go out verbatim.

### Triad

`backlog-index.sh` **62 ok** (47 → 62), docs_check 91/91, and the live tree
measured before and after. No Lean executed.

## 2026-08-24-qol-52 — a gate spec is code, and `IFS=';'` does not know that

`--gates` was split with `IFS=';'`, which is shell word splitting and knows
nothing about quotes. The ES lane's

```
python3 -c "import json; d=json.load(...); assert ...; print(...)"
```

became four fragments, each run as its own gate, each failing: a green build
with false GATE FAILED lines nominally about a JSON file, **not one of which
read the file**.

> "A red that looks like diligence is worse than no gate, because the natural
> repair is to make the red go away — which would have left the register
> permanently unchecked." (ES)

That sentence is quoted in the fix, because it is the reason this **refuses**
rather than repairing quietly: the fragments were not a broken gate, they were
a convincing one.

### Mechanism, and why refusing costs nothing extra

Detecting "a `;` inside quotes" needs the same quote-aware scan as splitting
correctly, so the two options cost the same and the tool does **both**:
`gate_split` splits only on **unquoted** `;` (so nothing can ever be silently
fragmented), and `gate_spec_refusal` refuses the ES shape at enqueue, before a
ticket exists. Measured: refuses `gate 4`, **0 tickets created**.

**One acceptance clause could not be taken literally.** "An unquoted `;` must
refuse" would refuse the **default floor itself** — its own two separators are
unquoted semicolons — and with them every tenure. The reading that survives
contact: an unquoted `;` that yields an **empty gate** (`a;; b`) is a stray,
and `run_gates` used to swallow it via `[ -n "$g" ] || continue`, so a
mistyped separator could remove a *check* without removing a *line*. That is
refused. A **trailing** `;` is measured, not assumed, and behaves differently:
command substitution strips trailing newlines, so no empty fragment ever
reaches the reader and nothing is lost — accepted, with a row saying so.

### And I broke a self-test into a real tenure while fixing it

To let a row call `run_gates`, I **moved** it above the self-test block with a
scripted slice. The move mangled the file: `--self-test` still parsed
(`SELF_TEST=1` confirmed by trace) but the guard never fired, and the run fell
through into a **real enqueue against the live queue**, waiting behind three
other lanes' tickets.

Nothing was left behind — the EXIT trap removed the ticket when `timeout`
killed it, verified against `/tmp/ls-build-queue` — but the lesson is the
lane's own: **a self-test that can reach the live queue is the ci.sh recursion
incident wearing different clothes.** Two corrections taken:

* **Nothing existing was moved in the re-application.** The three new
  functions go *above* the guard; `run_gates` stays exactly where it was. The
  rows that needed `run_gates` now assert on `gate_split`, which is the
  guarantee `run_gates` consumes — the honest test, and it needs no surgery.
* **Every debug probe now uses `LS_QUEUE`/`LS_LOCK` overrides.** Mine did not,
  for three probes, which is how a broken build reached the real queue at all.

Also re-learned: piping a hanging run to `tail` shows nothing, because the
pipe buffers. Redirect to a file — the same sizing lesson as the 64KB pipe.

### Triad

`triad.sh` **317 ok** (299 → 317), `--verify-guards` 32 ok, and check 87,
laws 45, sites 57, backlog-index 62, diagnose 51, new-proof 31, analogues 28,
substrate 25, editions 12, dupes 10, a6-guard 8, docs_check 91/91. Live queue
verified untouched (3 tickets). No Lean executed.

## 2026-08-24-qol-53 — the politeness line was reading a high-water mark

The C lane's finding, and it explains the whole day. `check.sh --iterate`'s
swap refusal read `sysctl vm.swapusage` **used** — swap *allocated and not
reclaimed*, a HIGH-WATER MARK. A box that swapped once had A17 closed for the
rest of its uptime. ~30 consecutive refusals, every lane forced into
one-shot-compile, three red tenures that a 15-second scratch check would have
caught — each paying a ~2000s queue cycle instead. All of it an instrument
artifact.

Re-measured here while writing the fix, every number at the same moment:

```
vm.swapusage used ....... 8630M of 10240M = 84.3%   -> REFUSED at the 50% line
memory_pressure ......... 52% system-wide FREE      -> 48% in use, permits
kern.memorystatus_vm_pressure_level ... 1 (normal)
load .................... 3.5 against a line of 10
```

> **A refusal is only as good as the quantity it refuses on, and a high-water
> mark is a record of the past wearing the units of the present.**

**The line did not move.** 50% stays exactly where it was — the finding was
the instrument, not the threshold, and the C lane's own reason for not
touching it holds: *"my lane is blocked" is the worst reason to move a shared
safety line.* Linux's `/proc/meminfo` SwapFree was already current-state and
is untouched. `LS_ITERATE_MAX_SWAP_PCT` still works as an alias so no
wrapper breaks.

**Every line now names its instrument and platform**, because "swap 88.5%" was
believable precisely *because* it was unlabelled:

```
memory pressure is 87.3% in use per memory_pressure:free%(macos), over the line of 50%
STATE  load 3.93 (line 10), memory pressure 50.0% (line 50%) via memory_pressure:free%(macos)
```

Both parsers are fixture-tested on **canned output**, since neither can be
exercised on the other platform's box: a recorded `/proc/meminfo` (50.0%,
plus the swapless-box case), this machine's verbatim `memory_pressure` text
(52% free → 48.0% in use), and the kernel-level fallback mapped onto the same
0-100 line (1→0 normal, 2→75 warn, 4→100 critical). The refusal path still
executes, and **absence is not pressure**: an unreadable instrument reports
`0 unavailable(no-instrument)` and PERMITS — a courtesy line that blocks
because it could not measure is this same defect one level down.

### A second stale number, found by my own probe

`stop_reason="$(machine_is_quiet)"` runs it in a **subshell**, so the numbers
that call measured died with it and the STOP line printed the values from the
**start** of the run — a fresh verdict beside a stale reading, the same family
as the bug being fixed. Called directly now, with the reason returned in
`QUIET_REASON`. Three rows pin it, including one asserting that the subshell
form loses them. **Fifth encounter with this trap** in this lane.

### Live, on this box, after

```
instrument : memory_pressure:free%(macos)
pressure   : 50.0% (line 50%)      load: 3.93 (line 10)
VERDICT    : PERMIT — iteration is open
```

**Worth flagging rather than acting on:** this box currently sits *exactly*
at the line, so iteration may flap here until memory frees. That is now a real
current-state signal rather than an artifact — but note the kernel's own
pressure level says `1 (normal)` at the same moment, which suggests
`100 − free%` is a stricter notion of pressure than the kernel's. Whether the
*number* should be the kernel level rather than the free complement is a
choice about a shared safety line, so it belongs to the C lane and the
coordinator, not to me.

### Triad

`check.sh` **104 ok** (87 → 104), and triad 317, laws 45, sites 57,
backlog-index 62, diagnose 51, `--verify-guards` 32, docs_check 91/91. No Lean
executed; live queue untouched.

<<<<<<< HEAD
## 2026-08-24-qol-54 — "first 8 of 46" was sorted, not first

pyc3's attempt-2 summary announced **"first 8 of 46"** and listed
`spec.lean:102-139`. The kept full log's FIRST error was `spec.lean:24` —
*maximum recursion depth*, a **different failure class**, of which the other
~44 lines were the cascade. The summary showed neither head nor tail and
dropped the only line of the causal class; the lane spent a diagnosis cycle
hunting `noncomputable` before opening the log.

> **"Truncation would have been harmless; a labelled-but-unfaithful sample is
> not, because what survives is a coherent wrong story."** (pyc3)

### The cause was `sort -u`, and the trap is lexicographic

The pool was built with `grep … | sort -u`, so `head -8` took the first eight
**in string order** while the label promised log order. And `spec.lean:102`
sorts *before* `spec.lean:24`, because `1` precedes `2`. The high line numbers
were not merely a different sample — **they were the ones that sorted first**,
which is why the real first error was not just missing but systematically
unreachable.

Reproduced on the fixture before fixing: the old sample's eight lines contain
`spec.lean:24` **zero times**.

### What it prints now

```
FIRST error (verbatim — later lines may be its cascade):
  error: LeanModels/Pyc/spec.lean:24:2: maximum recursion depth has been reached
next 7 of 41 more distinct, IN LOG ORDER (summary LOCATES; the full log COUNTS):
  error: LeanModels/Pyc/spec.lean:102:8: failed to synthesize Decidable (cascade)
  ...
```

The first error is printed **verbatim and unconditionally** — everything after
it may be its cascade, so it is the one line a summary may never drop — and
the remainder is deduplicated **in log order** (`awk '!seen[$0]++'`, never
`sort -u`). If a line says "next N", it is the next N as the build emitted
them.

### Two rows had pinned the defect

`check "the preview is LABELLED first 8 of 15"` and `"...the deduped pool is
2, and says so"` asserted the *label* — the exact promise the sample was
breaking — so they passed throughout. A row that checks the caption while the
picture is wrong is not a test of the picture. Both re-pointed at what the
summary can now keep, and the new rows assert the **content**: that the first
line printed IS the log's first error, that a sorted sample would have dropped
it, and that the remainder begins at the first cascade line.

### Triad

`triad.sh` **329 ok** (317 → 329), and check 104, laws 45, backlog-index 62,
diagnose 51, sites 57, `--verify-guards` 32, docs_check 91/91. Fixtures only;
the live queue was empty at the close. No Lean executed.
=======
---

## 2026-08-24-c-13 — INBOUND FROM THE C LANE: QoL lane's to renumber or close

*Id kept in the C namespace; nothing minted in the QoL sequence. Filed after
reading this file — A17's five flagged tightenings are yours and are not being
re-reported. This is a sixth, and it is about the INSTRUMENT rather than the
line.*

### `--iterate`'s SWAP LINE IS A HIGH-WATER MARK ON macOS, so A17 is a dead letter on this box

`tools/check.sh:302`, `read_swap_pct`, has two implementations:

* Linux — `/proc/meminfo` `SwapTotal`/`SwapFree`. **Current** usage: it falls
  when the pressure that caused it falls.
* macOS — `sysctl vm.swapusage`, field `used`. **Swap the kernel has
  allocated and not reclaimed** — a high-water mark that outlives the
  pressure, because macOS does not shrink swap files promptly.

So the 50% line means *"is swapping now"* on one host and *"has ever swapped
this much since boot"* on the other, and **a box that swapped once has A17
closed for the rest of its uptime.**

**Measured, on this machine, 2026-08-24.** `decide_iterate` refused ~30
consecutive attempts over the whole session, every one `refuse-swap` at
**88.5%**, while at the same moment:

| instrument | reading |
| --- | --- |
| `sysctl vm.swapusage` used | **88.5%** of 9 216 MB — over the line |
| `memory_pressure` | **"System-wide memory free percentage: 59%"** |
| `vm_stat` | 78 250 pages free, 253 176 inactive (16 KB pages) |
| load average | **2.42**, against A17's line of 10 |

Swap drained 8 274 MB → 8 154 MB in forty minutes, so the reading is not stuck;
it is simply not a pressure measurement. **The gate and the machine disagree by
construction, not by tuning.**

**The cost, measured rather than asserted.** The C lane's Rung A landing
(`2026-08-24-c-12`) is a 532-line proof written and ticketed **without a single
elaboration**, because the one licensed lock-free iteration never opened. That
is precisely the *"a 300-line proof at one compile per tenure is not a
session's work"* problem A17's own draft names, arriving through the gate
rather than around it.

> **A portable gate whose two implementations measure different QUANTITIES is
> not portable — it is two gates with one name, and the line only means what
> the instrument means.**

**Asked for: a pressure instrument on macOS, not a looser line.** Raising 50%
would be the wrong fix — it would loosen Linux, where the number is already
right. `memory_pressure`'s free-percentage line, or
`sysctl kern.memorystatus_vm_pressure_level` (1 = normal, 2 = warn, 4 =
critical), reports pressure rather than allocation. Keeping the swap reading as
a secondary on Linux costs nothing, and `--self-test`'s existing
`LS_MOCK_SWAP` case generalises to a `LS_MOCK_PRESSURE` one.

**Not touched by this lane, on purpose.** It is your gate, A17 is a draft, and
*"my lane is blocked"* is the worst available reason to move a shared safety
line — the same argument the C lane made for not lifting Go's run seam into
`Core` unilaterally.

*Renumber into your sequence or close it — the call is yours.*

---

## 2026-08-24-c-14 — INBOUND FROM THE C LANE: QoL lane's to renumber or close

*Id kept in the C namespace. Second inbound from this lane today; the first
(`2026-08-24-c-13`) you resolved as `2026-08-24-qol-53` inside the hour, and the
turnaround is why this one is filed rather than worked around.*

### `--build-target` IS PARSED AND THEN RESET TO EMPTY — the flag is a silent no-op

`tools/triad.sh`:

```
line 245 (inside the argument loop, 234-255)
  --build-target) need_val "$#" "$1"; BUILD_TARGET_ARGS="${BUILD_TARGET_ARGS:+$BUILD_TARGET_ARGS }$2"; shift 2 ;;

line 435 (the classification-state block, AFTER the loop)
  BUILD_TARGET_ARGS=""
```

The initializer runs **after** the parse, so whatever a lane passed is gone
before line 3007 (`for _bt in $BUILD_TARGET_ARGS; do add_build_target "$_bt"; done`)
ever looks at it. The comment at 431-434 has the design exactly right —
*"they cannot be UNIONed at parse time … so they are collected here and
applied after classification"* — and the collection variable is cleared
between the two halves it describes.

**MEASURED, four tenures, same invocation.** `--build-target "LeanModels.C
Examples.c.sunfish.stmt"` on `crunga` tickets 44165, 41896, 22930 and 80997.
In all four the build line read `lake build Examples.c.sunfish.expr
LeanModels.C.C23.Expr LeanModels.C` — the classifier's floor, verbatim — and
in all four **line 3008's `explicit --build-target: … (unioned; lane owes the
coverage statement)` never printed.** That absent line is the tell: the script
already knows to announce the union, so the union's silence is diagnosable
without reading the source.

**Why this is a §9.2-class defect and not a nit.** The `--gates` ruling this
file already carries convicts *"a gate set that shrinks without saying so"*,
and the `--classify-default` rejection convicts *"a default that makes a run
cheaper is a default that makes a claim smaller"*. This is the same shape a
third time, in the flag that exists **specifically** so a lane can build MORE
than the classifier's floor:

> **A flag whose whole purpose is to WIDEN a claim, and which silently does
> nothing, does not fail loudly — it produces a green whose coverage
> statement the lane writes in good faith and cannot support.**

The C lane's Rung A landing (`2026-08-24-c-12`) is the instance: the §5.4a
statement would have said *"and the four `Examples/c/sunfish` fixtures"*, and
one of the four — `Examples.c.sunfish.stmt`, the fixture that RUNS the tier's
call semantics — was never in the build. The gap was closed out of band, by an
A17 elaboration after the green (exit 0), which is only possible because your
`qol-53` fix reopened that door an hour earlier.

**The fix is a move, not a change**: hoist `BUILD_TARGET_ARGS=""` above the
argument loop with the other pre-parse initializers, or drop it (the parse's
`${VAR:+…}` idiom already tolerates an unset variable). Worth a `--self-test`
row asserting that `--build-target X` survives to `BUILD_TARGETS`, since the
existing row at 2502 exercises `add_build_target` directly and therefore
cannot see this.

*Renumber into your sequence or close it — the call is yours.*
>>>>>>> 17d1f7b

## 2026-08-24-qol-55 — a widening flag that did nothing, a condition that meant its opposite, and two gates wired

Four authorizations in one branch. Item 11 first, because it was live.

### Item 11 — the regression was mine, and the exposure is ZERO

`gates_planned` tested `CLASSIFY` where its own comment said **classify-only**.
`--classify-only` sets *both* flags, so the branch swept in the NORMAL
`--classify` ticket, returned an empty plan, and my item-6 empty-gate guard
refused it — **blaming a `;` the lane never typed**.

**It was latent until that guard existed.** Ordering, measured: the guard sits
at line 2768, the classify block at 2811, and `GATES="$(gates_compose "$FLOOR"
…)"` at **2892**. Every earlier reader of `gates_planned` ran *after* 2892, so
the wrong branch returned the right answer by accident. The guard was simply
the first caller to run before it. A comment saying "classify-only" over code
saying "classify" is the caption-vs-picture shape **in the condition**.

**Exposure audit, enumerated rather than assumed.** Counting `=== gate:`
invocations per tenure across every transcript on this box: every `--classify`
tenure that reported green ran **2–6 gates** — R-track's ten read 2,2,2,3,3,3,
3,3,6. Three tenures show zero (`go_triad2`, `go_t3`, `r3c-monadic-triad4`)
and **all three end still queued** — they never acquired the lock, never
reached the gate phase, and none reported green. **No green ever ran zero
gates.** The structural reason agrees: line 2892 populates `GATES` from the
class floor before the gate phase.

**The guard's message now distinguishes its two causes**, because only one is
the lane's: a stray `;` is something a lane typed, while an empty list from
`gates_planned` is a **tool defect** and now says so — *"tool defect, not your
command line… do NOT go looking for a stray ';' you did not type."*

### Item 10 — a widening flag that silently did nothing

`--build-target` was parsed at line 245 into `BUILD_TARGET_ARGS`, and the
variable was **initialised to empty at line 435, after the loop** — so the
union never saw it and the confirming line never printed. Reproduced before
fixing: `--build-target LeanModels.Extra` printed the "explicit --build-target"
line **0 times**. Hoisted above the loop; it now prints, and the build runs
`lake build LeanModels.Extra`.

> **A widening flag that silently does nothing produces an honest lane making
> a false coverage statement.** (crunga)

### The rows that could not have caught either

Both defects were invisible to rows calling the helpers **directly** — a flag
that never reaches a helper cannot be seen by testing the helper. The new rows
run the script the way a lane runs it (isolated lock and queue, stubbed
`lake`, no Lean, bounded), and **two existing rows had pinned the defects**:
one asserted `CLASSIFY=1 → gates as given`, which *was* the bug. Third
instance of caption-vs-picture in three consecutive items.

### Cosmetic, folded in

`--gates` naming a gate the floor already has printed it twice and ran it
twice. `gates_compose` now dedupes identical commands, order-preserving, so
plan, classification display and execution show one list. Deduping an
identical command is not shrinking a gate set.

### Items 7 and 2 — both gates wired

`step "lean-comment-forms" python3 harness/lean_comment_forms.py` — a full
step: tracked, argument-free (root defaults to `.`), no Lean, no network.
And with the tree at **zero malformed headings**, `--strict` is wired as
`backlog-headings`, using `--stdout` so CI renders without writing. Scoped
deliberately to headings: `--check` would also gate INDEX freshness, a
different promise and not this step's to make. Both pass on master's tree, and
`--verify-guards` covers both directions — a conforming backlog passes, a
malformed heading exits 3.

One row of mine needed anchoring: `grep -c 'backlog-index.sh --stdout
--strict'` counted **its own fixture line** and read 2 — the
fixture-is-not-enforcement trap, inside the row meant to enforce.

### Triad

`triad.sh` **343 ok** (329 → 343), `ci.sh --verify-guards` **39 ok** (32 → 39),
check 104, laws 45, sites 57, backlog-index 62, diagnose 51, new-proof 31,
substrate 25, analogues 28, dupes 10, editions 12, a6-guard 8, docs_check
91/91. Fixtures only. No Lean executed.

## 2026-08-24-qol-56 — index freshness is a different promise, so it is a different step

The approved follow-up to qol-55's scoping note. `docs/backlog/INDEX.md` is
GENERATED and committed, so a stale one is a file that matches no tree —
worth a gate. It is wired as `backlog-index-fresh` (`--check`), **beside**
`backlog-headings` (`--stdout --strict`), not folded into it.

**Why two steps and not one flag more.** "The headings are well-formed" and
"the generated file is current" fail for different reasons, are fixed by
different people, and take different actions to repair. A step that can go red
for two unrelated reasons tells its reader neither — the reader still has to
open the output to learn which promise broke, which is the whole cost a named
step exists to remove.

Demonstrated rather than argued, on one fixture:

```
baseline:            headings=0  freshness=0
after a hand-edit:   headings=0  freshness=1   <- only freshness fails
after a bad heading: headings=3  freshness=0   <- only headings fails
```

Each promise fails alone, and with its own exit code. `--check` without
`--strict` is silent on headings, so the separation holds in the tool as well
as in the wiring.

Four rows, both directions and the separation itself: the step exists as its
own step, its command carries no `--strict`, a freshly written index is in
sync, and a hand-edited one is DRIFT. stdout is dropped (the in-sync line);
the DRIFT report and its diff are on stderr and stay visible.

### One process note

The first attempt anchored the insertion on a literal containing an em dash
and asserted its way out — the assert fired *before* the write, so the file
was untouched and `--verify-guards` still read 39 ok, which is what said so.
Re-done with line-position insertion. A `cat -v | cut` on the same line had
already failed with `Illegal byte sequence`: **a multi-byte character in an
anchor is a matching problem in one tool and an encoding problem in the
next.** Anchor on ASCII, or anchor on position.

### Triad

`ci.sh --verify-guards` **43 ok** (39 → 43), backlog-index 62, triad 343,
check 104, laws 45, docs_check 91/91. All three live gates green on this tree:
headings 0, freshness 0, comment-forms 0. No Lean executed.

## 2026-08-24-qol-57 — a report has nothing to spend, so it has nothing to guard

Item 12, and the guard was mine twice over. `--classify-only` without
`--gates` died with *"gates_planned returned an EMPTY PLAN (tool defect…)"* —
a message I wrote to be helpful, firing on the tool's own report mode, killing
the banner it was about to print, on the Ada lane's most common invocation.

### The cut, and why it is neither option offered

The brief offered two: plan the class floor for display, or bypass the guard
with a report marker. Neither is quite it. **The display was never broken** —
the classify block already sets `GATES` from the class floor and prints it,
which is why `--classify-only --gates …` looked clean. The guard was asking a
question that has no answer *yet*, at a point where the answer does not
matter.

So the guard is split by what actually exists at that moment:

* **the lane's own spec** is whatever a lane typed, so it is validated
  whenever there is one — **including in report mode**, where the spec is
  DISPLAYED and a malformed one would be displayed wrong;
* **the composed plan** only means anything for a run that will RUN gates.

> **A report has nothing to spend, so it has nothing to guard.**

Verified across all four shapes: bare report `rc=0` and prints its
classification; report `--gates 'true'` clean; report with the ES-shaped
malformed spec **still refuses**, and with the *lane's* message
(`ONE COMMAND PER GATE`) rather than the tool's; real `--classify` tenure
runs its gates. Two rows go through `flagrun` — the bare invocation itself,
which is the only path that could have caught this.

### And a polarity the label invited

The coordinator misquoted `memory_pressure`'s FREE percentage as the pressure
reading. Their prose, not my tool — `read_pressure` returns in-use and always
did. **But the label was `memory_pressure:free%`, attached to a number that is
its complement**, so the output invited the misreading from its own line.

Naming the instrument was necessary and **not sufficient**: an unlabelled
POLARITY is the same defect one turn of the screw down. The label now names
the transform — `memory_pressure:100-free%(macos)` — and two rows pin it: the
label states the transform, and 52% free must read as `in-use`, not `free`.

Live, on this box, while writing it:

```
63.0 memory_pressure:100-free%(macos)     load 11.50, kern level 2
```

Which corroborates the coordinator's re-measurement (65–70% in use) and is a
REAL refusal now: the box is genuinely busy, and the load line fires first.

### Triad

`check.sh` **106 ok** (104 → 106), `triad.sh` **348 ok** (343 → 348),
backlog-index 62, laws 45, sites 57, `--verify-guards` 43, docs_check 91/91.
Fixtures only; live queue untouched. No Lean executed.

## 2026-08-24-qol-58 — the clause the gate lacked was exactly the incident it did not catch

Item 13: `harness/lean_comment_forms.py` gains the declaration-slot family's
general rule, after SV's seventh instance — a `/--` attached to a `#guard`.

> `/--` binds to the next DECLARATION; `/-!` stands alone; `#guard` / `#eval`
> / `#print` / `#check` are COMMANDS, not declarations.

**Why the case was invisible, and it was not the blacklist.** The scanner's
token reader accepted `[A-Za-z0-9_]` only, so a leading `#` stopped it dead
and every command follower read as the **empty token** — which is in no
blacklist and never will be. Adding `#guard` to the list alone would have
changed nothing. The reader now takes a leading `#`, and only `#`: `|`
(inductive constructor), `@[…]` (attribute) and `(` still read as the empty
token and stay legal.

**The prefix hazard is load-bearing, and both numbers were measured first.**
`#guard` is a prefix of `#guard_msgs`, which is **legal and is 42 sites on
master** — it takes `in` and attaches to what follows. Matching is whole-token
(the existing design), so those 42 stay silent; a prefix test would have
reported every one of them and red-lighted the tree. Would-be new defects
in-tree: **zero**, so the rule lands green — SV's instance is not on master,
which makes this preventive here.

The regression set **extends, not replaces**: 18 rows covering the four new
commands, `#guard_msgs` staying legal, the shapes the tree relies on
(declaration, theorem, structure field, inductive constructor, attribute,
`/-!` standing alone), the followers that were already illegal, and analog's
string-literal control — Go and SV both name `--` inside error strings. Wired
into `ci.sh`'s `selftests()` beside `docs_check.py`, because a fixture nobody
runs is not a fixture.

One expectation was wrong and the scanner corrected it: `/-- d -/ /-- e -/
def f` is **one** orphan, not two — the first comment dangles, the second
attaches to `def`.

### And master's self-test was already red, for everyone

Found while running the suite: `check "exe names are READ from the lakefile"`
asserted the literal list `leanmodels-run circuit-dc-runner`, so the C lane
adding a third `[[lean_exe]]` (`c-torture-run`, `1ef4a02`) turned
`triad.sh --self-test` red on clean master. Verified by stashing: it fails
without any of my changes.

**A row that pins another lane's data fails when they do their job.** What
that row is *for* is that the reader reads the lakefile — so it now counts
`[[lean_exe]]` blocks independently, checks every returned name against the
file, and asserts the runner the gates need is among them. Property, not
snapshot.

### The self-matching row, third time today

`grep -c 'lean_comment_forms.py --self-test' "$0"` counted **its own text**
and read 2. Same trap as the `--stdout --strict` row an item ago, and the
`sort -u` caption row before that. Anchored to the invocation line. Three
instances in one day says the reflex needed is: **a row that greps its own
file must anchor, or it will find itself.**

### Triad

`triad.sh` **350 ok** (348 → 350, and master un-redded), `lean_comment_forms`
**18 ok** (new), `ci.sh --verify-guards` **44 ok** (43 → 44), check 106,
backlog-index 62, laws 45, docs_check 91/91. All three live gates green:
comment-forms 0, headings 0, freshness 0. Live queue empty. No Lean executed.

## 2026-08-24-qol-59 — the item-12 residual is stale copies, and a courtesy scoped to one clone

Two things: a residual report answered by measurement, and item 14.

### The residual: current master is clean, and two OTHER lanes will trip

R-track reported `--classify-only` still tripping the empty-plan guard.
Reproduced on current master across **eight** shapes — bare, `--against HEAD`,
docs/tier/spine class, empty diff, `--gates-only`, and the two documented
contradictions (`--foreign`, `--since`) — and **not one emits EMPTY PLAN**.
The two `rc=2` results are the intended contradiction refusals, verified by
reading their messages.

Then the decisive test: the **pre-fix** `triad.sh` (`278e27f`, parent of
`40c093c`) trips on the identical fixture. So the trip is a stale copy, not a
missing shape — **no fix is needed**.

**But "rebase" is the wrong answer to give R-track.** Classifying every
lean-surfaces checkout on this box by content:

```
lean-softfloat  master             GUARD, NO FIX -> WILL TRIP
lean-ada        ada-m2-inch3       GUARD, NO FIX -> WILL TRIP
lean-surfaces   pyrebuild-monadic  no-guard (CANNOT trip)
lean-arch2 / lean-coord / lean-qol / lean-surfaces-wasm   guard+fix (fine)
lean-audit / lean-research                                 no-guard
```

R-track's own worktree carries `tools/triad.sh` as of **`b2150ae`**, which
**predates the guard entirely** — the string `EMPTY PLAN` is not in it, and
running it on the fixture produces the classification, not a refusal. So the
report cannot have come from that checkout as it stands now. The two
checkouts that *will* trip are **lean-softfloat** and **lean-ada**, both
confirmed by running their own copies.

A version skew that recurs is not a lane's carelessness; it is a missing
guard. `stamp_version_guard` already refuses a NEW enqueue from a worktree
whose `STAMP_VERSION` is behind master — it just doesn't fire here, because
this skew changed no stamp version. Widening it to "your triad.sh is behind
master's" would close the class. **Offered, not built.**

### Item 14: a courtesy protocol scoped to one clone

`check.sh` computed the target's path relative to its OWN clone and refused
anything outside, so the Lean tier's export corner — whose work lives in a
foreign `lean4export` checkout **by charter** — could never use `--iterate`.

> A courtesy protocol scoped to one clone is invisible to a lane whose work is
> in another.

The guard is **re-pointed, never removed**, and only on request: `--clone
<path>` or `LS_CHECK_CLONE=<path>`. The split that matters is which reads
follow the target:

* **target-relative** — its lakefile globs, its oleans, the directory the
  elaboration runs in, the axioms copy, and the guard itself;
* **charter-relative** — A17's own citation and this repo's backlog driver are
  claims about OUR repository and stay here;
* **machine-wide** — load and pressure are untouched. They have no clone.

**Resolved lazily, never defaulted.** The first cut assigned
`TARGET_CLONE="$CLONE"` once at startup, which FROZE it: nineteen self-test
rows that re-point `CLONE` for a fixture went on reading the real repo, and
said so immediately. Every consumer now spells `${TARGET_CLONE:-$CLONE}`, so
an unset opt-in follows `CLONE` wherever a caller moves it.

Seven rows through the flag path — the guard is in the main flow, so no
helper-level row can see it — with `LS_MOCK_LOAD=99` forcing an immediate
refuse-load so nothing elaborates: a foreign target refused by default, the
refusal naming the opt-in, `--clone` and `LS_CHECK_CLONE` both accepting it,
the run reaching the machine-wide lines afterwards, a bad `--clone` refused by
name, and the in-clone path unchanged.

### Triad

`check.sh` **113 ok** (106 → 113), triad 350, backlog-index 62, laws 45,
sites 57, comment-forms 18, `--verify-guards` 44, docs_check 91/91. Live queue
empty. No Lean executed.

## 2026-08-24-qol-60 — a version skew that recurs is a missing guard

Item 15: `triad.sh` refuses a NEW enqueue from a worktree running a
SUPERSEDED copy of itself.

### Identity, not ancestry — and the hazard that decides the design

A worktree on an old branch legitimately carries old shas, so ancestry says
nothing about which TOOL is running. The question asked is content identity:

> is my `tools/triad.sh` byte-identical to a PUBLISHED version of it that
> master has since replaced?

Three states, one test: matches the tip → current; matches an **older**
published version → superseded, refuse; matches **nothing** → local work,
allow. That last state is not a nicety. A bare "differs from master → refuse"
would refuse **every lane editing this tool**, starting with the one that
maintains the guard. A copy under development matches no published version, so
it is never behind.

### The object is the script that is RUNNING

The first cut hashed `$CLONE/tools/triad.sh`. Those are the same file in the
normal case and **not** the same when a current tool is pointed at another
checkout with `--dir` — there the tool enforcing the rules is the current one,
and refusing because the *other* tree carries an old copy is a wrong-object
refusal. §5.4b's pointer question, aimed at this guard. Now
`${BASH_SOURCE[0]}`, parameterised so fixtures can name a file.

Caught by testing, not by reading: running softfloat's and ada's own copies
returned "allowed" for both, because **their copies contain no guard at all** —
a superseded copy predates the thing that would refuse it. Which is the
honest limit of this guard, worth stating: **it cannot help a copy older than
itself.** It closes every skew that begins after it lands — refresh once, and
future drift refuses itself.

### Both tripwires were already gone

By the time it was built, softfloat's `triad.sh` was byte-identical to the
current tip: they refreshed on the coordinator's instruction. Nothing on this
box is superseded, which is why the fixtures matter — the live tree could no
longer demonstrate either direction.

End to end on a fixture upstream, running a superseded copy that DOES carry
the guard:

```
triad.sh: this worktree's tools/triad.sh is a SUPERSEDED version: byte-identical
  to master at 0174227, which is 1 published change(s) behind master (fd3888a)
  ON THAT FILE.
  Refresh it:  git checkout master -- tools/triad.sh     (or rebase this worktree)
```

**And the named remedy was executed, not just printed**: after
`git checkout master -- tools/triad.sh` the refusal is gone and the
classification prints. A refusal naming a fix that does not work is worse than
no refusal.

Enqueue-only by construction — it runs in the precondition block and nothing
calls it at acquire — so a ticket already in flight is untouched, per the
v1/v2 accept-and-log precedent. Absence is never a refusal: an unreachable
remote, and a path that does not exist, both allow.

### Triad

`triad.sh` **356 ok** (350 → 356), check 113, backlog-index 62, laws 45,
sites 57, comment-forms 18, `--verify-guards` 44, docs_check 91/91. Fixtures
only. No Lean executed.
