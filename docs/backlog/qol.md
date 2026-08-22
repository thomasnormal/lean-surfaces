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
