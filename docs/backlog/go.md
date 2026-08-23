# The Go lane's backlog

Per-lane file per `docs/family-architecture.md` §9.5. **Appended only by the
Go lane.** Ids are `YYYY-MM-DD-go-<n>` and need no reservation, because the
lane name makes them unique. Entries newest-last.
The founding charter is `docs/go-charter.md`; the founding landing is
`docs/backlog.md` §L76.

---

## 2026-08-22-go-1 — RUNG 1'S SCOPE IS DERIVED: coverage is CONJUNCTIVE, and the charter's "21" was wrong (formerly `§G1`)

Rung 1's scope was not chosen. It was measured, by a reach-ladder mode
added to the census instrument, and the measurement changed both the
scope and one of the charter's published numbers.

### The instrument, and why the ladder is a different question from the census

`harness/go/construct_census.go` gains two modes, `--ladder` and
`--kindsets`. **Default output is untouched, verified by `--compare`
exiting 0 against the committed rung-0 census** — the on-touch rule's
byte-identical test, met.

The census aggregates kinds across a corpus, which answers *what is in
there*. It cannot answer *what would I have to build next*, because **a
file is reachable only when EVERY kind it uses is modelled**. Reach is a
property of a file's whole kind SET, so adding a kind unlocks a file only
when it was that file's LAST missing one. `--ladder` computes the greedy
curve; `--kindsets` dumps per-file kind sets so any candidate scope can
be scored without re-parsing 5,419 files. Both are deterministic
(double-run byte-identical, verified).

### THE HEADLINE: coverage is conjunctive, so bundles do not compose

Measured on the Go 1.25.6 standard library — 5,419 files, 0 unparsed:

| scope | files | % |
| --- | ---: | ---: |
| rung 0's 28 kinds | 512 | 9.4 |
| + VALUES alone | 728 | 13.4 |
| + CONTROL alone | 713 | 13.2 |
| + DECLS alone | 550 | 10.1 |
| **CONTROL + VALUES + PAREN + DECLS** | **3,084** | **56.9** |

**No bundle alone clears 14%, and together they clear 57%.** That is the
finding that shaped the rung: shipping any one of them would have bought
almost nothing, and the cumulative curve's knee is DECLS — `DeclStmt` +
`TypeSpec`, **two kinds, 31.1% → 56.9%, +1,400 files.**

**The sharpest instance reproduces the C tier exactly.** `docs/c23-goal.md`
§4 found that `SwitchStmt` alone cleared zero tests. Here: adding
`SwitchStmt` to rung 0 unlocks **nothing** (512 before, 512 after);
`CaseClause` alone likewise **512**; **both together, 514** — two files.
The switch family only pays once the rest of the rung is present, which
is why it is IN this rung rather than its own. Two languages, two
corpora, same shape.

The greedy ladder's marginal column is therefore an **order artifact and
must not be quoted as importance**: it credits `CaseClause` with +1,212
files, but that is only true after twenty-one other kinds are present.
The ladder is recorded in `docs/go-reach-ladder.json` (24 steps) with
this caveat attached.

### RUNG 1's SCOPE, and the fixture

**45 kinds — rung 0's 28 plus seventeen — reaching 3,084 of 5,419 files
(56.9%).**

    CONTROL  ReturnStmt IfStmt BranchStmt SwitchStmt CaseClause
             EmptyStmt LabeledStmt
    VALUES   StarExpr ArrayType CompositeLit KeyValueExpr IndexExpr
             SliceExpr StructType
    PAREN    ParenExpr
    DECLS    DeclStmt TypeSpec

`Examples/go/rung1/rung1.go`: 178 lines, **one import (`fmt`)**, 532
nodes, 45 kinds, census in `docs/go-rung1-census.json`.

It preserves rung 0's design property — the split observable. `total` and
`count` are invariant under every schedule; arrival order and the
per-worker split are not. **Verified over 530 runs** — 300 consecutive, a
`GOMAXPROCS` sweep over 1/2/4/8/16 at 40 each, and 30 under `-race` —
byte-identical output every time, zero race reports. Same standard rung 0
was held to.

**The census caught a regression in the fixture's first version**, which
is the reason to census a fixture at all: it scored **43** kinds, not 45,
because it had no `select` — writing rung 1 had silently DROPPED
`SelectStmt` and `CommClause` from the modelled vocabulary while
appearing to widen it. **A rung must be a superset of the one below.**
The check is now a one-line assertion on the two censuses and it is what
found this.

### THE CHARTER CORRECTION — "21 kinds" was wrong, and the cause is instructive

`docs/go-charter.md` §7.2 published the remainder as **21 kinds**. It is
**24**: 52 − 28 = 24, and the ladder independently produced exactly 24
steps.

The 21-item list was computed against the driver's **pre-rewrite**
vocabulary of 31 kinds — before §7.1's `sync.WaitGroup` join was replaced
by a counted channel receive, an edit that removed `StarExpr`, `DeclStmt`
and `DeferStmt` from the fixture and therefore *added* them to the
remainder. The count was never re-derived after the rewrite that
invalidated it.

**This is the failure mode `--compare` exists to prevent, hit in PROSE
rather than in JSON.** The instrument's own numbers are gated and cannot
drift; a charter's derived numbers are not, and this one drifted the
moment the artifact it described changed. Recorded as an argument for
extending census coverage to the charter's derived figures, not only the
instrument's. The charter now carries the correction inline rather than a
silent edit.

### Triad

Classified by `tools/triad.sh --classify` as **tier**, and the
classification is a conservative over-read worth recording rather than
arguing with. **No Lean in this landing** — the change set is `docs/`,
one Go fixture and one Go instrument.

`classify_path()` maps `Examples/*` to tier **by path, unconditionally**,
and `Examples/go/rung1/rung1.go` is the single file that triggered it.
Measured, that fixture is invisible to lake: nothing imports it
(`grep -rn "Examples.go" --include=*.lean` is empty), and the `Examples`
library's glob is `Examples.+`, which matches Lean MODULE names — a `.go`
file has no module name. The sibling rule already gets this right for the
other file: `harness/*` correctly classified `harness/go/construct_census.go`
as docs. The rule is right for `Examples/**/*.lean` and over-broad for
native-source fixtures, which every language lane will eventually land.
**Reported to the coordinator; not downgraded by lane discretion** —
conservative over-classification is the correct default.

**A build is nonetheless genuinely owed, for an unrelated reason**, and
it is not this diff's fault: `lake build --no-build` exits 3 in this
clone, because it was seeded by `cp -Rpc` (A13) from a sibling at an
older master and reset to `2d0ba41` without rebuilding. A green here
would attest to the clone's freshness, not to this change's safety.

A ticket is **enqueued** (`--lane go`, queue position 4 behind leantier,
basecase and wasm) and its result is reported in the next entry. This
lands ahead of it under the zero-Lean rule; the FIFO queue means the wait
is latency and not the starvation that cost this lane four handoffs
during the founding.

* `gofmt -l` clean on both Go artifacts; `go vet` clean.
* rung-0 census `--compare` **exit 0** (default output unchanged by the
  two new modes) — the on-touch byte-identical test.
* rung-1 census `--compare` **exit 0** agreeing, **exit 5** on drift, and
  the drift halts under `set -e`. The §9.1 audit found three `--compare`
  implementations that exit 0 on drift; **this instrument is not one of
  them**, re-verified here on both censuses.
* `--ladder` and `--kindsets` double-run byte-identical.

### Next

The Lean half: `LeanModels/Go/` on `Core.SemM`. **`Core.SemM` has not
landed** (`LeanModels/Core/` is `Basic.lean` only), so it is defined BY
SHAPE with the adoption note, per the ES lane's precedent — `W` = the
envelope's store shape, `ρ` = panic, refusals in `Halt`, `lang_version`
per file per the envelope design. Statement discipline from theorem one:
spec half separate from interpreter half (STMT-65, cookbook §6).

---

## G2 — M1 INCH 1: the substrate by shape, and the zero-UB finding becomes UNREACHABLE-BY-CONSTRUCTION (2026-08-22)

The Go lane's first Lean. Values, the substrate, rung 1's abstract syntax
and its first statement walker, and 27 specification lemmas.
**1,066 lines across six modules**, no `sorry`, no `native_decide`.

### The substrate — written by shape, then REPLACED by Core mid-landing

This inch was authored against a by-shape substrate with the ES lane's
adoption note, because `LeanModels/Core/` was `Basic.lean` only.
**`LeanModels/Core/Outcome.lean` landed at `376735e` while the inch was in
flight, and the local copy was REPLACED by the import — replaced, not
wrapped.** Verified mechanically: the Go lane now defines **none** of
`SemM`, `Halt`, `Loud`, `refuse`, `exhausted` or `raiseIn`, and a grep for
those definitions in `LeanModels/Go/` returns nothing.

The migration cost less than it might have because the by-shape copy had
the same layer order Core does — `ExceptT ρ (StateT W …)`, `StateT` inside
— for the same stated reason. The whole edit was the import, deleting the
local `Halt`, and re-pointing the interpreter-half lemmas at Core's API
(`SemM W ρ α` unfolds to `W → Except Loud (Except ρ α × W)`, so applying
the computation to a world IS the run; Core exports no separate `run`).

**AND IT SURFACED A GAP IN CORE, reported rather than worked around.**
Core's `Loud` has exactly two constructors — `timeout` and
`unsupported (msg : String)` — and its header states that a tier needing
more causes *"does not extend this type; it adds an `.except` layer of its
own"*. But `docs/family-architecture.md` §5.2 requires the **four** refusal
causes be *"reported separately"* precisely because *"pooling them makes
the scoreboard unreadable"* — and a `String` payload means a scoreboard
must **parse prose** to bucket a refusal. This lane is the first to need
the four on top of Core (only `LeanModels/Python/Monadic/Substrate.lean`
imported it before), so the collision had not been hit yet.

The interim: the Go tier keeps `RefusalCause` and `SpecRef` as its own
types and `renderRefusal` writes them into Core's string with a stable
prefix — `[<cause-tag>|<doc>:<section>] <prose>` — where the tag is the
family's own name for the cause (§5.2's `unsupported`, `undefined`,
`environment`, `order-dependence`) spelled explicitly rather than via
`repr`, so the scoreboard key survives any rename of the Lean constructor.
Bucketing is then a prefix test rather than a search, which is mechanical
but still parsing. **A structured payload in Core would be better and the
coordinator has the argument.**

* **W = `GoWorld`** — the envelope's store, plus `locals` mapping names to
  **addresses** rather than values, because Go locals are addressable and
  rung 1's fixture takes `&x`. Plus `lang : LangVersion` **per file**, and
  `sched : Schedule` carried from the first commit while `Schedule` is a
  one-element type no rule reads (`docs/go-charter.md` §6.2's one
  non-negotiable structural commitment).
* **ρ = `Panic`, and it carries an IDENTITY as well as a value.** The
  identity is not decoration: the spec's `recover` rule turns on *which*
  panic is in flight, since a deferred function that panics replaces the
  panic it was handling. A ρ carrying only a value cannot tell a re-panic
  from what it replaced.

**And Go's four exits do not all go in ρ, which is where this lane
diverges from ES on purpose.** ES put all four abrupt completions in ρ
because ES2026 writes `? Foo(x)` at 2,328 sites and `ExceptT`'s bind IS
that operator. Go has no such operator, and its exits differ in kind:
`panic` unwinds across frames running deferred work and is observable by
`recover` — ρ; `return`/`break`/`continue` are ordinary structured
control flow that never cross a frame uninvited and that `recover` cannot
see — so they are a `Flow` in α, which is the Python tier's shape. Putting
them in ρ would force every deferred-function rule to distinguish "a panic
is in flight" from "a return is in flight" — precisely the distinction
`recover` is defined by.

### THE ZERO-UB GATE — from quotable to unreachable

`docs/go-charter.md`'s headline is that **"undefined" appears zero times
in the Go specification** (C23: 284, plus Annex J.2's 221 enumerated
circumstances). `docs/family-architecture.md` §4.3's Go row asks that the
emptiness be **gated**. It now is, and by the strongest available means:

`RefusalCause` carries all four family causes **including `undefined`** —
deleting it would make the emptiness unstatable. The gate is a second,
narrower type: **`GoRefusal`, with three constructors and no `undefined`**,
and every refusal the tier emits goes through `SemM.refuseGo`, whose cause
argument is a `GoRefusal`. So cause 2 is not empty by convention, nor by a
grep a new call site could slip past — **it is unreachable by
construction**, and `goRefusal_never_undefined` proves the image excludes
it. A future rung that genuinely found undefined behaviour in Go would
have to widen the type deliberately, which is the right price.

Checked, not asserted: `grep` confirms **zero** raw `SemM.refuse` call
sites remain in the walker, and a guard pins that `undefined` is a REAL
constructor (`undefined ≠ unsupportedConstruct`) so the gate is a
restriction rather than a statement about an empty type.

**Integer overflow is where this pays.** The specification's "Integer
overflow" defines BOTH signednesses — unsigned "computed modulo 2ⁿ";
signed "may legally overflow and the resulting value exists and is
deterministically defined … **Overflow does not cause a run-time panic. A
compiler may not optimize code under the assumption that overflow does not
occur.**" `docs/c-tier-charter.md` §2.2(a) needed two rules and a refusal
between them. Go needs one function, `IntKind.wrap`, and no refusing arm
at all. Guarded: `int8` 127+1 = −128 **through the walker**, not merely in
the arithmetic helper.

**Division by zero is the control case.** "Run-time panics" makes it a
defined panic, so it goes to ρ — guarded to produce a `Panic` carrying the
runtime's message and, explicitly, to produce **no refusal at all**.

### STMT-65, and the split came out at 63%

Spec half separate from interpreter half from theorem one, by the
cookbook's axis — *does the STATEMENT mention the interpreter?*

**Measured on this file: 17 spec-half lemmas, 10 interpreter-facing = 63%
mathematics.** The family's estate measured **65%** surviving a definition
swap. Landing within two points of that on the first Lean file is not a
coincidence — it is what following the law prospectively buys, rather than
discovering the ratio afterwards.

The temptation the cookbook names showed up exactly as advertised: it is
easier to state *"the walker never refuses undefined"* than *"`GoRefusal`'s
image excludes it"*. The second is the spec-side fact, so the gate lives
there — and the interpreter-side corollary then costs one line
(`refuseGo_cause_never_undefined`) and carries no content of its own.

### The build hook, and no spine edit

`LeanModels` is a `lean_lib` with **no glob**, so nothing under
`LeanModels/Go/` is built on its own. `Examples/go/rung1/guards.lean`
imports `LeanModels.Go`, and the `Examples.+` glob pulls the whole lane
into the default targets and CI — **with no edit to `LeanModels.lean` or
`lakefile.toml`, both of which `tools/triad.sh` classifies as spine.**
That is `docs/c-tier-charter.md` §4.8's precedent, which also records that
taking the authorized spine import anyway was measured unnecessary, tried,
and reverted.

### The battery

**28 `#guard`s**, all passing: integer overflow both signednesses, the
per-file version predicate, flow short-circuiting, and the walker on
programs — declare/assign/binary, `++`, both `if` branches, address-of
then dereference, `return` and `break` stopping a sequence, a labelled
empty statement, and the four refusal rows.

**Non-vacuity was RUN, not assumed**: flipping the signed-overflow value
and flipping the zero-UB row to claim `goto` refuses as `undefined` each
make Lean report the failing expression; restoring rebuilds clean.

Axioms on the recorded theorems: `propext` and `Quot.sound` at worst —
several depend on **no axioms at all**.

### Triad

* `lake build LeanModels.Go` and `Examples.go.rung1.guards` green;
  authored lock-free per rule 3 — every module built in isolation at
  `nice -n 19`, the largest an **11-job** target, none near the 100-job
  threshold. Re-verified after the Core migration, including both
  non-vacuity flips.
* `docs_check` green.
* Ticketed with explicit `--gates`, since this landing DOES carry Lean —
  unlike §G1, which landed under the zero-Lean rule. **Green**, and
  `--classify` scoped the build to this lane's seven modules rather than
  all default targets:

  | arm | result |
  | --- | --- |
  | `lake build` (scoped: `LeanModels.Go.*` + the guards) | **exit 0** |
  | `docs_check` | **83/83**, 32 illustrative-exempt |
  | `diff_test` | **1,427 cases, 0 failed** (1,309 matched, 118 whitelisted) |
  | `script_corpus` | **65 scripts, 0 failed** (50 matched, 15 loud-blocked) |

  The build arm returned in **one second**: every module had already been
  elaborated lock-free during authoring, so the tenure bought
  verification under the lock rather than the compute. That is the
  lock-free authoring rule paying for itself — the ticket queued **3h47m**
  and then held the machine for **84 seconds**.

**§G1's ticket came back GREEN and is recorded here** rather than left
dangling: `lake build` exit **137 (OOM) on the first attempt**, which
`triad.sh` correctly classified as a resource kill and re-ran rather than
reporting red — exit **0** on attempt 2, BUILD GREEN; `docs_check`
**83/83**; `diff_test` **1,427 cases, 0 failed** (1,309 matched, 118
whitelisted). That is the third distinct time this lane has met exit
137/143 under load, and the second time the retry logic turned it into a
green rather than a false red.

### Next

Inch 2: the `switch` family and `TypeSpec`, which the ladder showed are
the rung's remaining weight — and `for`, which is where `LangVersion`
stops being a predicate with three guard rows and starts being a branch
in the loop rule.
## INBOUND FROM THE SOFTFLOAT LANE — `2026-08-22-softfloat-4` (Go lane's to triage)

*Filed by the SoftFloat lane during its consumer census
(`docs/softfloat-charter.md` §2.4). Id kept in the SoftFloat namespace.*

### §3.5.3 LISTS GO AS A SOFTFLOAT CONSUMER; NO GO ARTIFACT MENTIONS FLOATS

`docs/family-architecture.md` line 1772:

| Go | `float32`/`float64` | same component, no new work. |

**Measured — zero occurrences of `float`, case-insensitive, in every Go
artifact in the tree:** `docs/go-charter.md`, `docs/backlog/go.md`,
`docs/go-construct-census.json`, `docs/go-rung1-census.json`,
`docs/go-reach-ladder.json`. And `LeanModels/Go/` does not exist.

The row is an architecture-lane inference, and *"same component, no new
work"* is probably true when Go arrives — the point is only that **it is a
prediction, not a demand**, and SoftFloat's priorities are set from demand.

**What this lane needs from you, when convenient:** whether `float32`/`float64`
are in your rung-1 scope. If they are, Go is a second consumer of
`LeanModels.SoftFloat` — which is also §3.8's named trigger for moving the
component into `LeanModels/Core/`, so your answer has a structural consequence
beyond your own tier.

### ANSWERED BY THE GO LANE — no, and the census is the reason

**`float32`/`float64` are NOT in rung 1's scope, deliberately.**

The measurement: rung 1 is 45 `go/ast` node kinds (§G1), and floats are
not excluded *syntactically* — a float constant is a `BasicLit`, which is
in the vocabulary. They are excluded in the **value model**: `GoVal`
(`LeanModels/Go/Value.lean`) has `boolV`, `intV`, `stringV`, `ptrV`,
`chanV`, `structV`, `sliceV` and `nilV`, **and no float constructor**. A
float literal therefore reaches the walker and refuses as an out-of-tier
construct rather than being silently truncated.

Two notes for your priorities:

* **Your census row is now stale in one detail** — it said *"`LeanModels/Go/`
  does not exist"*. It does, as of §G2. The `float`-count-of-zero finding
  was correct when taken and is correct again now: the six modules of
  §G2 contain no float.
* **`docs/family-architecture.md` §3.5.3's row is a fair prediction, and I
  am not disputing it** — when Go does take floats, `float32`/`float64`
  are IEEE-754 binary32/binary64 and I would expect to be an ordinary
  consumer with no new component work. I am confirming only that the
  demand is **not yet**, so it should not raise SoftFloat's priority on my
  account.

**When it changes:** Go's spec ties floats to the same "Integer overflow"
neighbourhood this tier already mirrors, and my charter's §9 float
question is gated behind the sequential ladder's remaining rungs
(`switch` family, `TypeSpec`, `for`). I will file an inbound to your lane
the moment a float constructor enters `GoVal` — which is also the moment
Go becomes §3.8's second consumer, with the structural consequence you
name.


---

## G3 — THE LOCAL `RefusalCause` IS RETIRED: the class was making a round trip through a string (2026-08-23)

Core's payload landing (`f714f76`) gave `Loud.unsupported` a typed cause,
and records this lane as the **third tier** to have re-derived §5.2's four
classes locally. The coordinator migrated the tier mechanically and left
one decision open. **Verdict: retire the local enum, and read the cause as
data.**

### What was retired, and why it had to be

The tier adopted Core when `Loud.unsupported` held a bare `String`, so it
kept its own four-class `RefusalCause`, a `tag` function, and
`renderRefusal`, which wrote `[<tag>|<doc>:<section>] <prose>` into the
message. The guards then recovered the class with `String.startsWith`.

That was the right shape while Core could not hold the class. It is the
wrong shape now, and the argument is Core's own: its header states that a
scoreboard *"buckets on THIS, never by parsing the payload's prose — the
entire reason the class is a constructor and not a string convention."*
Keeping the prefix would leave **the class making a round trip through a
string that exists only because the typed field did not**.

Retired: the local `RefusalCause`, `RefusalCause.tag`,
`RefusalCause.toCore`, and `renderRefusal`. The two taxonomies were
already the same four classes under the same four names — this tier's
`tag` and Core's `className` returned byte-identical strings — so the
collapse loses nothing. Verified by grep: no prefix is built and none is
parsed anywhere in the lane.

**The message is prose again.** The payload landing deliberately kept the
prefix byte-for-byte so nothing downstream of the text moved; that was the
conservative call and correct at the time. The only consumer of that text
was this lane's own guards, so removing it moved nothing else. The
now-stale note in `Sem.lean` saying the prefix is retained was corrected
rather than left to rot.

### THE GATE SURVIVED AND GOT SHORTER

`GoRefusal` — three constructors, no `undefined` — stays. It is still this
tier's own type and still the reason cause 2 is unreachable here. What
changed is what it maps into and what the gate is stated against:

* `GoRefusal.toCore : GoRefusal → SpecRef → RefusalCause SpecRef`, so the
  cited clause rides as the constructor's payload.
* The gate is now `(r.toCore π).isUndefined = false`, proved
  `cases r <;> rfl` — **stated against Core's `isUndefined`, which Core
  lifted from the ES lane precisely so the gate is written once per family
  rather than once per tier.** This lane's contribution is the narrower
  `GoRefusal`; the predicate is everyone's.
* Non-vacuity is still pinned, and it too moved onto Core's predicate:
  `(RefusalCause.undefined π).isUndefined = true`. Without that row the
  gate would pass for the wrong reason if `undefined` were ever dropped.

### What reading the class as data BUYS, beyond deleting code

Two guard shapes that were not expressible while the class lived in a
string, both now in the battery:

* **The clause is checkable.** `refusalClause` reads π structurally, so a
  guard pins that `goto` refuses citing the spec's `Goto_statements` and
  an unbound identifier cites `Declarations_and_scope`. Previously the
  citation was inside the prose.
* **The gate is checkable per-refusal.** Four guards assert
  `RefusalCause.isUndefined = false` on the four refusals the walker
  actually emits — the executable companion to the theorem that covers
  all of them.

Battery: **34 `#guard`s**, up from 28. Non-vacuity RUN on both new shapes
— claiming `goto` is `undefined`, and claiming the wrong cited clause,
each make Lean report the failing expression; restoring rebuilds clean.

### Triad

Authored lock-free per rule 3; every module rebuilt in isolation at
`nice -n 19`, the largest an 11-job target. Axioms unchanged: `propext`
and `Quot.sound` at worst, several theorems depending on none.

**Tenure GREEN**, read from the full log rather than the summary:

| gate | result |
| --- | --- |
| `lake build` (scoped: `LeanModels.Go{,.Sem,.Spec}` + the guards) | **exit 0** |
| `docs_check` | **87/87** marked blocks, 35 illustrative-exempt |
| `diff_test --no-build` | **1,427 cases, 0 failed** — 1,311 matched, 116 whitelisted |
| `script_corpus --no-build` | **65 scripts, 0 failed** — 50 matched, 15 loud-blocked |

Queued **76 minutes**, held the machine **91 seconds**. The whitelist moved
118 → **116** and matched 1,309 → **1,311** against §G2's run: two cases
that were whitelisted-unsupported now MATCH. Neither is this lane's —
nothing here touches the Python tier — but it is the direction the
scoreboard is supposed to move, and worth recording because a whitelist
that only grows is the failure mode the no-whitelist rule exists to
prevent.

**§G2's tenure closed GREEN** and is recorded here: `lake build` exit 0,
`docs_check` 83/83, `diff_test` **1,427 cases, 0 failed** (1,309 matched,
118 whitelisted), `script_corpus` **65 scripts, 0 failed**. The ticket
queued **3h47m** and held the machine **84 seconds** — lock-free authoring
meant the tenure bought verification, not compute.

---

## G4 — INCH 2'S CENSUS: `fallthrough` is 4%, the loop-var delta is 21,715 sites, and `for {}` is the commonest loop (2026-08-23)

Census-first, before a line of inch 2's semantics. §G1's reach ladder said
*which* kinds to add; it could not say what they COST, because a node
count cannot see a construct's sub-forms. `SwitchStmt: 5,186` says nothing
about how many carry a `fallthrough`. So the instrument gained a `shapes`
field and the Go 1.25.6 standard library was re-censused.

**The instrument was cross-validated before it was believed.** The
counters were first written as a scratch program, then folded into
`harness/go/construct_census.go`; both produce identical numbers on all
fifteen counters. Committed censuses regenerated, and all three gates
re-verified: agree → 0, agree → 0, drift → 5, double-run byte-identical.

*(A summarizer bug was caught and is worth one line, because it is the
failure mode this project names: an `awk` pass computing the ratios
matched `switch_total` as a SUBSTRING of `typeswitch_total` and reported
`fallthrough` at 27.2% and "switch with default" at 320.6%. The raw counts
were always right; the derived line was not. A ratio above 100% is the
kind of wrong answer that announces itself — the dangerous version is the
one that lands at 27% and looks plausible.)*

### The switch family — cheaper than its ladder position suggests

| shape | n | of 5,186 switches |
| --- | ---: | ---: |
| **`fallthrough`** | **208** | **4.0%** |
| with an init clause | 258 | 5.0% |
| with a `default` | 2,456 | 47.4% |
| tagless (`switch { case cond: }`) | 1,052 | 20.3% |
| ≤3 cases | — | **63.8%** |
| ≤7 cases | — | 91.3% |

Type switches: **766**, of which **4** carry an init clause. Case
expressions: **22,671 single-expression against 3,297 multi** — 87% of
non-default cases test exactly one value, with a tail reaching a single
276-expression case.

**The decision this makes: `fallthrough` is a rung of its own, not part of
inch 2.** It appears in 4% of switches, and it is the one switch feature
that breaks the clean reading of a case body as an independent block — it
makes the body's exit depend on the NEXT clause. Deferring it keeps 96% of
switch sites reachable and keeps the rule compositional. The init clause
(5%) defers with it for the same price.

### The loops — where `LangVersion` stops being a predicate

| shape | n | of parent |
| --- | ---: | ---: |
| `for` total | 22,853 | — |
| **bare `for {}`** | **10,733** | **47.0%** |
| `for` declaring vars (`:=`) | 8,519 | 37.3% |
| `range` declaring vars | 13,196 | **98.4%** of 13,412 ranges |
| **loop-var delta sites** | **21,715** | — |

Two findings, and both change inch 2's shape:

**`for {}` is the single commonest loop form at 47%.** It has no
condition, so termination is entirely the body's business — which makes it
exactly where **fuel stops being a formality**. `docs/statement-cookbook.md`
§5's fuel-placement question is not deferrable past this construct, and
`LeanModels/Core/Outcome.lean`'s header is explicit that fuel is an index
on the step function and never a monad layer.

**The Go 1.21→1.22 delta touches 21,715 sites in the standard library
alone.** §G2 landed `LangVersion.perIterationLoopVars` with three guard
rows and no consumer; inch 2 is where it becomes a branch in a rule. The
charter's §3.3 acceptance test — the model must produce `[3 3 3]` and
`[0 1 2]` from byte-identical bodies in one package — is inch 2's, and
the census says the branch it depends on is not a corner case.

Labelled control flow stays small: **183 labelled `break` (1.1%)** and
**174 labelled `continue` (2.2%)**. `goto`: 583. The inch-1 walker already
returns `Flow.broke`/`Flow.continued` carrying an optional label, so
resolution is a bounded addition rather than a redesign.

### `TypeSpec` — structs, and almost nothing else

**11,264 type declarations: 8,156 structs (72.4%)**, 2,670 other (23.7%),
**438 interfaces (3.9%)**, 185 aliases, 68 generic. Inch 2's `TypeSpec`
work is struct declaration; interfaces are a later rung and the census
says they are 4% of the surface, not a co-equal half.

### Inch 2's scope, derived

1. `TypeSpec` over struct types, and `DeclStmt`'s remaining forms — the
   `+1,400`-file knee §G1 measured.
2. `SwitchStmt`/`CaseClause`, **excluding `fallthrough` and init clauses**
   (96% and 95% of sites respectively).
3. `ForStmt` including bare `for {}`, which forces the fuel decision, and
   `RangeStmt` — carrying the go1.22 branch, with §3.3's acceptance test
   as the gate.

Deferred with a measured price rather than a shrug: `fallthrough` (4%),
switch init (5%), type switches (766 sites, and they need `go/types`),
interfaces (3.9%).

**A fixture gap the census found in this lane's own artifact:**
`Examples/go/rung1/rung1.go` exercises one switch with four cases and a
default, but **no `fallthrough` and no type switch** — consistent with
deferring both, and recorded so the rung-2 fixture is written knowing it.

### Triad

Docs and one harness instrument; **no Lean**, so no tenure owed. `gofmt -l`
clean, `go vet` clean, both committed censuses regenerated and their gates
re-verified, `docs_check` green.

---

## G5 — INCH 2: the §3.3 acceptance test PASSES, and one program means two things (2026-08-23)

Inch 2 on §G4's census: struct declarations, the go1.22 loop-variable
BRANCH with the charter's §3.3 acceptance test as the gate, bare-`for`
fuel semantics stated, and `fallthrough` deferred as its own rung.

### THE GATE: `docs/go-charter.md` §3.3, discharged

The charter set the family's copies-vs-deltas acceptance test and was
blunt about it: *"If the architecture cannot express that program, it is
wrong regardless of how faithful either individual version-mirror is."*

**It passes.** One `loopVarProbe`, one walker, one field of the world
different:

    runUnder go1.21 loopVarProbe "changes" == some 1
    runUnder go1.22 loopVarProbe "changes" == some 3

The observable is **pointer identity, not closure capture** — the same
thing §3.2 measured on the real toolchain, where collecting `&i` across
iterations gave *"1 distinct address under go1.21 and 3 under go1.22."*
The probe counts how many times `&i` changes across three iterations, so
the Lean model and the `go build` run are answering the same question with
the same number.

**Non-vacuity RUN, in both directions, because a version branch that does
nothing would pass a one-sided test:**

* claiming go1.21 also yields 3 — i.e. no branch at all — **fails**;
* claiming the counting loop breaks under go1.22 — i.e. freshening
  without the copy-back — **fails**.

The second is the charter's named trap: *"An implementation that freshens
bindings without the copy-out passes every closure-capture test and
silently corrupts ordinary counting loops."* So `countProbe` runs exactly
five times under **both** versions, and that row is as load-bearing as the
delta row. The spec's two halves are implemented as two halves: fresh
LOCATIONS per iteration, and the previous iteration's VALUE copied in.

**The loop-variable set is READ OFF, not declared.** Whatever `init` binds
is the set — the locals added since the enclosing scope. A hand-maintained
list would be a second place to get the same fact wrong.

### Bare `for {}` — the fuel semantics, stated

47.0% of the standard library's `for` loops (§G4). With no condition,
nothing but fuel bounds it:

* `execStmt 0 _` and `execSeq 0 _` are **`Halt.timeout`**, never a
  refusal — Core's `exhausted`, and the family's rule that exhaustion has
  exactly one outcome.
* `execLoop 0 none none [] []` is `timeout`: the bare loop's own semantics.
* **`break` still escapes one**, guarded — so the exhaustion above is the
  loop terminating on fuel, not a walker that cannot leave a loop. Without
  that row the timeout row would pass for the wrong reason.

**The walker now recurses on FUEL ALONE**, not lexicographically on
(fuel, statement). Core's header is explicit that fuel is an index on the
step function and never a monad layer, *"because hidden in state it is not
an argument and the interpreter fails to show termination."* Recursing on
fuel makes that argument trivial; the price is that nesting depth draws on
the same budget as iteration, which is a stated cost rather than a
discovered one.

*Termination shaped the code once more, visibly:* `evalExpr`'s composite-
literal arm first evaluated fields while walking the type's DECLARED
order, and Lean rejected it — `find?` loses the structural link to the
literal. Fields are now evaluated by structural recursion over the
literal (`evalFields`) and then placed in declaration order. The
definition is better for it, and the reason is recorded next to it.

### Structs — 72.4% of type declarations

`TypeSpec` over struct types, keyed composite literals, and field
selectors. Keyed form only: the positional form depends on declaration
order, which is a typing question `go/types` answers and this walker does
not. An absent field takes the zero value (`nilV` at this rung — field
types are a later rung's census); a key the type does not declare is a
**refusal**, not an invention, and so is a literal of an undeclared type.

### `fallthrough` — DEFERRED AS ITS OWN RUNG, at a measured 4.0%

**208 of 5,186 switches** (§G4). It is the one switch feature that breaks
reading a case body as an independent block, because the body's exit
depends on the NEXT clause. Deferring it keeps **96% of switch sites**
reachable and keeps the rule compositional. Switch init clauses (5.0%)
defer with it for the same reason and the same price.

It refuses as an **out-of-tier construct, never as undefined behaviour** —
guarded twice, once on the class and once on `isUndefined`, so the
deferral cannot quietly become a UB claim.

### The statement split moved, and the direction is honest

**17 spec-half, 12 interpreter-facing — 58.6% mathematics**, down from
§G2's 63%. Inch 2's additions are fuel theorems, and the cookbook says
plainly that *"fuel thresholds do not transport at all."* A rung that
adds loops SHOULD move this ratio down; a rung that added loops and left
it at 63% would mean the fuel facts had been written into spec-shaped
statements, which is §6's named trap. Recorded as a measurement rather
than smoothed over.

### Battery

**46 `#guard`s**, up from 34. New: structs (field read, zero-fill, two
refusal shapes), the §3.3 pair, the copy-back pair, bare-`for` timeout,
`break` escaping a bare loop, and the `fallthrough` deferral pair. Axioms
unchanged — `propext` and `Quot.sound` at worst, several theorems
depending on none. No `sorry`, no `native_decide`.

### Triad

Authored lock-free per rule 3; every module built in isolation at
`nice -n 19`. **Tenure GREEN**, read from the full log:

| gate | result |
| --- | --- |
| `lake build` (scoped: `LeanModels.Go{,.Sem,.Spec,.Stmt}` + guards) | **exit 0** |
| `docs_check` | **87/87** marked, 35 illustrative-exempt |
| `diff_test --no-build` | **1,427 cases, 0 failed** — 1,311 matched, 116 whitelisted |
| `script_corpus --no-build` | **65 scripts, 0 failed** — 50 matched, 15 loud-blocked |

Queued **76 minutes**, held the machine **102 seconds** — the build arm
returned in one second, every module having been elaborated lock-free
during authoring. The Python tier is unmoved at every number, which is
what a landing confined to `LeanModels/Go/` must produce.

---

## G6 — INCH 3: the model reproduces a REAL crypto function, 35 rows, and the expected column was generated (2026-08-23)

Suite-driven, no pet programs. The census picked the exemplar, the
exemplar picked the operators, and the oracle wrote the expectations.

### THE CENSUS — what the walker still refuses inside what rung 1 reaches

Rung 1's vocabulary reaches 3,084 of the standard library's 5,419 files.
That is a claim about the INGESTER. The sharper question is what the
WALKER refuses inside those files, and it has a different answer:

| construct | reachable files using it | share |
| --- | ---: | ---: |
| **`CallExpr`** | **2,261** | **73.3%** |
| `ArrayType` | 1,479 | 48.0% |
| `IndexExpr` | 874 | 28.3% |
| `RangeStmt` | 676 | 21.9% |
| `SliceExpr` | 541 | 17.5% |
| `FuncLit` | 442 | 14.3% |
| `SwitchStmt` / `CaseClause` | 432 / 430 | 14.0% |
| `GoStmt` / `ChanType` / `SendStmt` / `SelectStmt` | 26 / 26 / 19 / 10 | ≤0.8% |

**Files ENTIRELY within what the walker stepped before this inch: 633.**

Two findings. **Calls are the single biggest unlock at 73.3%** — nothing
with a function in it runs without them, which is most of Go. And the
concurrency constructs this tier was chartered for are **under 1%** of
rung-1-reachable files: they are not where the sequential ladder's weight
is, which is the census agreeing with the charter's own sequencing note
rather than contradicting it.

### THE EXEMPLAR — chosen by search, not by taste

A second census swept every non-generic, non-method function in the
standard library for ones the walker could execute, then filtered to those
that RETURN a value and do real arithmetic. 751 candidates on the loose
filter; the tight one surfaced this:

    // bitLen is a version of bits.Len that only leaks the bit length of
    // n, but not its value.
    func bitLen(n uint) int {
        len := 0
        for n != 0 { len++; n >>= 1 }
        return len
    }

`src/crypto/internal/fips140/bigmod/nat.go` — **FIPS-140 crypto code**,
a better provenance than anything this lane would have written. Vendored
verbatim beside the model in `Examples/go/bitlen/bitlen.go` with its
BSD-3-Clause attribution, under §1.4's ruling that the in-tree copies are
taken under the repository's single instrument.

**The exemplar chose the operators, which is the point of picking from the
corpus.** `n >>= 1` forced compound assignment and the shift operators;
`for n != 0` forced a condition-only loop; the function boundary forced
calls. Nothing was added because it looked useful. The bitwise
`&`/`|`/`^`/`&^` family is deliberately NOT declared — no exemplar needed
it, and declaring an operator the walker refuses would be a vocabulary
claim the tier cannot honour.

### THE DIFFERENTIAL — and the expected column was GENERATED

**35 rows**, sweeping the powers of two and their neighbours to the full
64-bit width. The model, executed in Lean's kernel, reproduces what the
`gc`-compiled function printed on every one, including `2^64 − 1 → 64`.

**The first version typed the expected column by hand, and that was the
wrong way round.** This file's whole claim is that two independent
implementations agree; a hand-copied expectation makes the Lean side the
source of both columns the moment someone "fixes" a row. The rows are now
`printf`-ed from the compiled binary and mechanically rewritten into
`#guard` syntax. Recorded because the hand-typed version *passed* — it
would have shipped looking identical and meaning less.

Non-vacuity RUN: flipping `bitLen (2^64−1)` to 63, and flipping the fuel
row to claim 4 fuel suffices for a 64-bit walk, each make Lean report the
failing expression; restoring rebuilds clean.

**What is claimed and what is not.** These rows are a differential claim —
model and toolchain agree on this function. They are **not** a proof that
`bitLen` is correct. `bitLen n` = the number of significant bits of `n` is
an induction over the loop and is this lane's next theorem, not this
inch's. The distinction is written into the file so a later reader cannot
mistake one for the other.

### Fuel is load-bearing here, not decorative

The loop runs once per significant bit, so `bitLen (2^63)` needs 64
iterations. Guarded: at fuel 4 the answer is **`timeout`** — the model
declines — and at 4,096 it answers. A wrong number at low fuel would be
the failure this rung exists to prevent.

### Calls, and where an undeclared one lands

A call to a function the program does not declare is **`environment`**,
not a language gap: it retires by widening the modelled slice, never by
climbing a rung. Guarded on `bits.Len`, and guarded again on
`isUndefined` being false — the standing gate, now reaching calls.

Arguments are evaluated in the CALLER's frame before any parameter is
bound, which is the spec's order and matters when an argument names a
variable the callee also has. A `break` or `continue` that would cross a
function boundary refuses rather than escaping.

**`FuncTable` is a parameter, not world state.** `GoWorld` is declared
before `Stmt` and cannot mention it — but the better reason is that a
function table does not change as a program runs. Threading it says so,
and keeps `GoWorld` about the things that move.

**Fuel reached expressions at this rung, and calls are why.** Expression
evaluation was structural and total until now; a call can recur, so
`evalExpr` takes fuel and the two evaluators merged into one mutual block.

### Battery and split

**88 `#guard`s** — 46 at rung 1, 42 on the exemplar. Statement split
unchanged at **17 spec / 12 interpreter**: this inch added no theorems,
which is honest — its result is differential, not deductive, and inflating
the spec half with restatements of what the guards already check would be
the §6 trap in the other direction.

Axioms unchanged: `propext` and `Quot.sound` at worst. No `sorry`, no
`native_decide`. A stray unused binder the linter flagged was removed
rather than silenced.

### Standing

`fallthrough` stays deferred until its rung (4.0%). The MM-oracle is
untouched pending Thomas's ruling — and this inch's census is the first
evidence bearing on its timing: the concurrency constructs are under 1% of
rung-1-reachable files, so the sequential ladder is not being starved by
waiting.

### Triad

Authored lock-free per rule 3. **Tenure GREEN**, read from the full log:

| gate | result |
| --- | --- |
| `lake build` | **exit 0**, 3,721 jobs, zero failed targets |
| `docs_check` | **87/87** marked, 35 illustrative-exempt |
| `diff_test --no-build` | **1,427 cases, 0 failed** — 1,311 matched, 116 whitelisted |
| `script_corpus --no-build` | **65 scripts, 0 failed** — 50 matched, 15 loud-blocked |

Queued **106 minutes**, held the machine **37 minutes** — and the second
number is the one worth recording, because it is 25× the previous inch's
91 seconds. **Adding `Examples/go/bitlen/` made `--classify` widen the
build target from four Go modules to the whole `Examples` library**, which
pulled in the Python tier's heavy proof files (`pins_search` alone is 54
seconds). Nothing was wrong and nothing failed; the tenure simply cost
what a whole-library target costs. Worth knowing before the next inch adds
a directory: a new `Examples/` subdirectory is not free, and the classifier
is right to be conservative about it.

The Python tier is unmoved at every gate number, which is what a landing
confined to `LeanModels/Go/` and `Examples/go/` must produce.

---

## G7 — INCH 4: `bitLen` gets its SPEC HALF proved, and the call census corrects §G6's reading (2026-08-23)

### THE `--build-target` QUESTION, answered mechanically

**It cannot scope down.** `tools/triad.sh`'s own comment is explicit —
*"UNION, never replace — a lane can always build more"* — so a lane may
widen its build but never narrow what `--classify` computed.

**The widening's cause was found rather than guessed**, by running
`path_targets` on each file of the last landing:

    Examples/go/bitlen/guards.lean -> Examples.go.bitlen.guards
    Examples/go/bitlen/bitlen.go   -> Examples          ← the 37 minutes
    Examples/go/rung1/guards.lean  -> Examples.go.rung1.guards

`path_targets` maps `Examples/*.lean` to its own precise module, and every
OTHER `Examples/` path to the whole library. The cost came from the
**vendored `.go` reference file**, not from the Lean. And it was not a
build input by any reading: no `[[input_dir]]` covers `Examples/go/` (they
cover `Examples/spice/*.cir` and `Examples/verilog-a/*.{va,json}` only),
and the sole mention of it in any `.lean` was prose inside a docstring.

**Fixed at this end rather than escalated**: the source is now quoted in
`guards.lean`'s docstring — verbatim, comments and all, with the same
BSD-3 attribution — and the sibling file is deleted. `path_targets` now
returns the precise module for everything this lane owns. Quoting costs
nothing and keeps the tenure scoped.

**Still worth a QoL ruling, and it is the coordinator's to route:** the
`Examples/*` catch-all is correct for fixtures a library reads and
over-broad for reference material that nothing builds. An extension-aware
arm, or a way for a lane to declare a path non-input, would fix it for
every language lane that wants to vendor a source beside its model — which
is all of them.

### THE CALL CENSUS — and it CORRECTS a reading of §G6

§G6 measured that `CallExpr` appears in **73.3% of rung-1-reachable
files** and called it the biggest unlock. True, and this census measures
the other axis — call SITES, of which there are 526,571:

| call shape | n | share |
| --- | ---: | ---: |
| **`pkg.F(…)` / `x.M(…)` — selector** | **275,975** | **52.4%** |
| plain identifier — *what this tier models* | 194,580 | 37.0% |
| builtin | 45,995 | 8.7% |
| other (through a value, a literal, …) | 10,021 | 1.9% |

**Both figures are true and they measure different things, which is worth
being exact about rather than quoting the flattering one.** Calls unlock
73.3% of FILES; the calls this tier models are 37.0% of call SITES. The
majority shape is the selector — and a selector call is
`pkg.F` or `x.M` **indistinguishable without `go/types`**, which is why
they are one bucket here and why they are the extractor's problem before
they are the walker's.

Function declarations, 63,697 of them: **44,309 plain, 19,388 methods
(30.4%)**. Results: 41% return nothing, **47% return exactly one**, 11.5%
return two or more. Params: 0→15,452, 1→29,503, 2→10,287. Variadic 668,
generic 387 — both under 1%.

**So inch 4's call work was largely done in inch 3**, and the census says
so plainly: single-result calls to plain names cover 47% of declarations
and 37% of sites, and everything beyond needs `go/types`. Multi-result
returns (11.5%) are the next honest widening; methods and selectors wait
on the extractor.

### THE THEOREM HALF — `bitLen`'s specification, PROVED

STMT-65's split, applied to a real function.

**§1 SPEC HALF — no interpreter, no world, no fuel.** `bitLenSpec` is
what the Go loop computes, written as mathematics, and two theorems
bracket it:

* `bitLenSpec_lt : n < 2 ^ bitLenSpec n`
* `bitLenSpec_le : 0 < n → 2 ^ (bitLenSpec n - 1) ≤ n`

Together: `2^(k-1) ≤ n < 2^k` for `k = bitLenSpec n`, which **is** the
definition of bit length — not a restatement of the code. Both by strong
induction on `n`. Axioms `propext, Quot.sound`; no `sorry`.

**§2 THE BRIDGE — one step, and it is the load-bearing one.**
`shr_one_is_halving` proves the interpreter's `n >>= 1` on a `uint64` IS
the spec's `n / 2`, resting on `fdiv_two` (halving a non-negative integer
is floor division). This is where a width or signedness bug would
surface, and it is the single place the two halves touch.

**What is still OWED, named rather than implied.** The full interpreter
half — *the walker, run on `bitLenBody` with enough fuel, leaves `len`
equal to `bitLenSpec n`* — is an induction over the loop carrying the
store through each iteration. It is the next theorem. What is proved is
its arithmetic step; what is CHECKED is the composition. Writing the
distinction into the file is the point of separating §1 and §2 at all.

### THREE-WAY AGREEMENT

The same 35 inputs are now checked against **two independent standards**:
what `gc` printed, and `bitLenSpec` — which §1 proved is genuinely the bit
length. A model agreeing with the compiler but not the mathematics, or the
reverse, shows up in exactly one block. Non-vacuity run on both: flipping
an oracle row and flipping a spec row each make Lean report it.

### Battery

**123 `#guard`s** — 77 on the exemplar (35 oracle, 35 spec, plus width,
fuel, and refusal rows), 46 at rung 1. **6 proved lemmas** in the
exemplar. Axioms `propext`/`Quot.sound` at worst. No `sorry`, no
`native_decide`.

### Triad

Authored lock-free per rule 3. **Tenure GREEN**, read from the full log:

| gate | result |
| --- | --- |
| `lake build` (scoped: **`Examples.go.bitlen.guards` alone**) | **exit 0** |
| `docs_check` | **87/87** marked, 35 illustrative-exempt |
| `diff_test --no-build` | **1,427 cases, 0 failed** — 1,311 matched, 116 whitelisted |
| `script_corpus --no-build` | **65 scripts, 0 failed** — 50 matched, 15 loud-blocked |

Queued 41 minutes, held the machine **129 seconds** — against the previous
inch's 37 minutes. **The classifier was fixed upstream between the two
tenures** and now says so by name: *"'Examples/go/bitlen/bitlen.go' is a
non-Lean fixture, unreferenced by any Lean module or gate corpus —
invisible to lake, classified docs."* So the widening is closed at both
ends: the file is gone from this lane, and the rule that widened on it no
longer does. The build target is a single module and the class is `tier`
with `tiers none`.

`fallthrough` stays deferred (4.0%); the MM-oracle is untouched.

---

## G8 — THE LOOP INDUCTION IS NOT LANDED, and the selector question is an EXTRACTOR decision (2026-08-23)

Two items, and the first one is a partial. Reporting it as a partial is
the point.

### (1) THE OWED INDUCTION — substrate landed, theorem NOT

The debt was: *the walker, run on `bitLenBody` with enough fuel, leaves
`len` equal to `bitLenSpec n`*. **It is not proved, and this entry does
not claim it is.**

**What landed** is the substrate it rests on, and it is reusable by every
later theorem about mutation rather than by `bitLen`'s alone —
`docs/statement-cookbook.md` §9's frame predicates, stated about pure
world functions so they mention no interpreter and sit in the spec half:

* `wRead_wStore_same` — a write is visible where it was written;
* `wRead_wStore_other` — **a write is invisible everywhere else**, the
  frame half, resting on
* `find_filter_ne`, proved by induction on the store because the library
  shapes did not line up and an explicit induction is cheaper to keep
  than a fragile rewrite;
* `wLookup_wStore` — a write moves no binding.

**What blocked it, named precisely so it is findable work rather than a
shrug.** The induction needs to step the walker, and stepping it means
reducing `GoM = ExceptT Panic (StateT GoWorld (Except Loud))` applied to a
world. That reduction is not `rfl`: `lookupLocal name w` is **not**
definitionally the match on `w.locals.find? …` — checked, it fails — so
every step needs a rewrite through the monad stack, and this lane has no
lemma set for that. The Python lane solved the same problem with
`py_simp` and an `Obs` spine over many sessions; the Go lane needs its
analogue, and **that** is the next piece of work, not more proof attempts
against a bare `simp`.

**Landing the substrate and naming the blocker beats a `sorry`**, and it
beats thrashing: the alternative on offer was a half-reduced proof carried
across sessions, which is the shape this project's covenant exists to
refuse. The debt stands, its size is now known, and its prerequisite has a
name.

The statement split moved **17/12 → 20/12 = 62.5% mathematics**, up from
inch 2's 58.6%, because frame predicates are spec-half by construction.

### (2) DECISION BRIEF — selector calls, for the coordinator

§G7 measured selector calls at **275,975 — 52.4% of all call sites**, and
said they need `go/types`. That was too coarse. Split by receiver shape:

| selector call shape | n | of selectors | of ALL calls |
| --- | ---: | ---: | ---: |
| **`pkg.F(…)`** — receiver is an imported package name | **83,276** | **30.2%** | 15.8% |
| **`x.M(…)`** — receiver is a plain identifier: a METHOD | **162,628** | **58.9%** | 30.9% |
| `a.b.M(…)`, `f().M(…)`, `arr[i].M(…)` — chained | 30,071 | 10.9% | 5.7% |

**The finding that changes the decision: package calls do NOT need
`go/types`.** A call is `pkg.F` exactly when the receiver identifier is an
imported name in that file, and the extractor already parses the import
table. It is a **syntactic** resolution — 30.2% of selectors, resolvable
with an import map and no type checker at all.

The other 69.8% do need types: to resolve `x.M()` you must know `x`'s type
to find `M`'s declaration. **So methods come with the expensive tier and
not the cheap one** — which answers the third question directly: yes,
the 30.4% of declarations that are methods arrive together with
`go/types`, because they are the same problem.

**The trap in the cheap tier, and it is why this is a decision and not an
obvious yes.** Resolving `pkg.F` syntactically buys the ability to *name*
the callee — it does not buy the ability to *run* it. Running needs the
package's semantics, and the corpus calls **438 distinct standard-library
packages** with a long tail: the top 12 are only **57.6%** of package
calls, `fmt` alone 12.8%, and the list includes `unsafe` (8,966) and `C`
(1,833), neither of which this tier will ever execute.

So the honest value of cheap-tier resolution is **a better refusal, not a
wider reach**: `environment`, naming the package and the function, instead
of an undifferentiated "selector call". That is worth something — it is
exactly the bucket `docs/family-architecture.md` §5.2 says must retire by
widening the slice rather than by climbing a rung, and a scoreboard that
can rank the 438 by frequency can *pick* what to model next. But it is not
reach, and pricing it as reach would be the motivated error.

**What the brief recommends, for the coordinator to rule on:**

1. **Do the cheap tier in the extractor**, not the walker: emit a resolved
   callee (`package`, `function`) on every `pkg.F` call site, from the
   import table. No `go/types`, no new Lean.
2. **Treat the resulting refusals as a ranked worklist.** 438 packages,
   57.6% in twelve — that is a census the tier can act on.
3. **Defer `go/types` until a consumer needs it.** It buys methods (58.9%
   of selectors) and chained receivers (10.9%) *together*, at the cost of
   a type checker in the extraction path — a large, single, indivisible
   step. Nothing on the current ladder needs it, and the exemplar that
   would justify it has not been found yet.

No implementation was done and none is proposed here.

### Triad

`fallthrough` stays deferred (4.0%); the MM-oracle is untouched. Ticketed
with explicit `--gates`; verdict below.

---

## G9 — THE AUDIT'S THREE ROWS, all fixed, and one of them caught this lane failing its own rule (2026-08-23)

`docs/quality-audit-2026-08-23.md` "## go". Three rows, none high, and the
first is the one worth the entry.

### 1. The non-vacuity section checked NOTHING — and it is this lane's own rule

`Examples/go/bitlen/guards.lean` carried a section headed *"a differential
row that cannot fail is decoration"* whose rows were **byte-identical to
ordinary oracle rows above it**. So the section asserting that the harness
can fail was itself decoration. **The rule was this lane's, written in
this lane's own words, and this lane broke it one inch later.**

Worth being exact about how: §G6 caught a *confusing* `!=` row, replaced
it with `bitLen 1024 == some 11` for clarity — and that is precisely the
oracle row from §3. The fix for a legibility problem introduced a
duplication problem, and nothing checked for duplication.

**Fixed by making the rows a different KIND of check.** They now assert
NEGATIVES, which no oracle row does: the model does not answer a
neighbouring value (`some 10`, `some 12`), and does not answer `none` (a
refusal or an exhaustion). Together they say the harness would notice
either failure mode. Verified non-vacuous by flipping one to `== true` and
watching Lean report it.

The stronger check — that a wrong EXPECTATION breaks the build — stays a
flip test, run and recorded, and deliberately not in the file: a guard
that must fail is not a guard.

### 2. `LeanModels/Go/Stmt.lean`'s header was stale by three inches

It still described the file as rung 1's syntax at rung 1's figures, after
inches 2–4 had added struct declarations, the go1.22 loop-var branch,
bare-`for` fuel, calls, compound assignment and shifts. Replaced with a
table of what each inch added, and — the part that was actually
misleading — a note that **the 56.9% figure is a property of the INGESTER
vocabulary and has not moved**, while what moved is how much of it the
WALKER steps. §G6's 633-files figure is the one to quote for the walker.
Two numbers that measure different things, which is the same distinction
§G7 had to draw for calls.

### 3. The oracle column shipped without its generator

The vendored `bitlen.go` said *"NOT compiled as part of this repository"*,
so the `"what gc printed"` column had no reproducer. (The file itself is
already gone — inch 4 inlined it to stop the classifier widening the build
— but the point survived the file.)

The docstring now carries the generator: the exact `printf` shape, the
build-and-run command, and **`go1.25.6 darwin/arm64`** pinned. And it was
checked rather than asserted: re-running the documented command and
diffing against every `#guard` in the file gives **35 rows, 35 pairs, zero
mismatches**. The column is reproducible from the file alone.

### Why all three are the same defect

None was a wrong answer; all three were **provenance decaying out from
under a correct one** — a rule restated until it stopped biting, a header
describing an older file, a column whose generator walked away. The
instrument's `--compare` exists to stop exactly this in JSON. §G1 already
recorded it happening in prose (the "21 kinds" figure); these are three
more, and the pattern is now named three times in this lane.

### Triad

**Tenure GREEN**, read from the full log:

| gate | result |
| --- | --- |
| `lake build` (scoped: `LeanModels.Go{,.Spec,.Stmt}` + the exemplar) | **exit 0** |
| `docs_check` | **87/87** marked, 35 illustrative-exempt |
| `diff_test --no-build` | **1,427 cases, 0 failed** — 1,311 matched, 116 whitelisted |
| `script_corpus --no-build` | **65 scripts, 0 failed** — 50 matched, 15 loud-blocked |

Queued 100 minutes, held the machine **66 seconds**.

`fallthrough` stays deferred (4.0%); the loop induction stays owed with
its blocker named (§G8: the lane needs a `SemM`-reduction lemma set, the
analogue of the Python lane's `py_simp`, before the induction is
attemptable); the MM-oracle is untouched.

---

## G10 — THE SEAM: one lemma opens the stack, and §G8's three "unprovable" lemmas are four lines each (2026-08-23)

### THE CENSUS FIRST — what Python actually has, and why Go's answer is cheaper

§9.0a: census the lemma, not just the obligation. Measured on the tree:

| artifact | size | what it actually contains |
| --- | ---: | --- |
| `LeanModels/Python/Obs.lean` | 158,701 B, **79 theorems** | `fuelMono` over a nine-function mutual block, the `Res.le`/`Run.le` approximation orders, and the congruences `Run.le_bind`, `Run.le_bindE`, `Run.le_ite`, `Run.le_withLocals`, `Run.le_toWorld` |
| `LeanModels/Python/Monadic/Substrate.lean` | 10,603 B | §1 the `Run σ` ↔ family-stack isomorphism proved both ways, §2 Python's named refusals, §3 the frame/world zoom, and `liftRes` |

**And the census found the thing that changes the estimate: Python has no
opener, because it never needed one.** `Run` is a DATATYPE — its `bind`
reduces by cases, so the wall Python hit was the approximation-order
congruences, not the unfolding. `GoM` is a transformer STACK, so the
opener is exactly what was missing. **Different wall, and Go's is one
lemma wide.** Quoting Python's 79 theorems as the price would have been
the wrong read of a real number.

§3.4's ruling was taken as written: **the ORDER lifts, the CONGRUENCES
don't** — each is about a different monad's `bind`, and Python's `Res`
carries an `.exn` arm this stack does not, so a lifted congruence would be
the thick-trunk mistake. Core supplies the order; this lane supplies its
own congruences.

### THE SEAM — `LeanModels/Go/Obs.lean`, 126 lines, 10 rows

**One opening**, per §3.4's *"one opening of the monad stack is the right
number"*:

    run_bind : (x >>= f) w = match x w with
      | .error h            => .error h                  -- loud, state discarded
      | .ok (.error e, w')  => .ok (.error e, w')        -- panic, state RETAINED
      | .ok (.ok a, w')     => f a w'                    -- continue

Then the primitives every `do` block bottoms out in — `pure`, `get`,
`set`, `modify`, `refuseGo`, `exhausted`, `raiseIn` — and two corollaries,
`map` via `map_eq_pure_bind` and the value-discarding sequence. **`map`
needs no second opening, which is the point of having exactly one.**

All ten tagged `@[go_run]`, the simp set **named once** in `SpecAttr.lean`
beside `go_spec`, registered there for the same import-boundary reason.

The three outcome rows are the covenant made mechanical: a refusal
discards state and cannot be caught, a panic RETAINS it, and only a value
continues. That is the layer order paying for itself in a form a proof can
rewrite with.

### §G8's BLOCKER IS CLEARED — and the receipts are the lemmas it named

§G8 recorded three lemmas as unprovable and named the cause: *"`lookupLocal
name w` is NOT definitionally the match on `w.locals.find? …`"*. That was
correct and is still correct. With `go_run` opening the stack, each is now
**four lines**:

* `lookupLocal_ok` — name resolves to its address, world unchanged;
* `loadAddr_ok` — an address reads its value, world unchanged;
* `storeLocal_ok` — **a write lands in exactly the world §1.3b's frame
  lemmas describe.**

That last one is the join the induction needs: §1.3b's `wStore`/`wRead`
carry the frame reasoning on the PURE side, and `storeLocal_ok` is the
bridge from the monadic step to it. The two halves now meet.

Axioms: `run_bind`, `lookupLocal_ok`, `storeLocal_ok` all depend on
**`propext` alone**. No `sorry`, no `native_decide`.

### What this does and does not settle

**Settles:** the reduction problem. Stepping the walker is now a rewrite
with a named set rather than a per-proof excavation, and the three
step lemmas exist.

**Does not settle:** the loop induction itself. It still needs the
`for`-loop's own congruence — the `ite` shape over the loop condition, and
the recursion on fuel — and those are §3.4's remaining five shapes,
landing when a consumer needs them. **The debt is smaller and its next
step is mechanical rather than open-ended**, which is the difference
between §G8's entry and this one.

Split moved **20/12 → 20/15**; the three new rows are interpreter-facing
by construction, since they are statements about the walker's helpers.

### Triad

**Tenure GREEN**, read from the full log:

| gate | result |
| --- | --- |
| `lake build` (scoped: `LeanModels.Go{,.Obs,.Spec,.SpecAttr,.Stmt}`) | **exit 0** |
| `docs_check` | **91/91** marked, 35 illustrative-exempt |
| `diff_test --no-build` | **1,427 cases, 0 failed** — 1,311 matched, 116 whitelisted |
| `script_corpus --no-build` | **65 scripts, 0 failed** — 50 matched, 15 loud-blocked |

Queued **92 minutes** (sixth in a six-deep queue at its worst), held the
machine **65 seconds**.

`fallthrough` deferred (4.0%); MM-oracle untouched.

---

## G11 — THE WALKER IS PROVED THROUGH A MUTATION, and the blocker moved again (2026-08-23)

The loop induction is **still not closed**. But the debt is a different
size and a different shape, and both halves of the last two inches paid
for themselves on one goal.

### PROVED — one full turn of the loop

**`body_step`**: `len++` then `n >>= 1` takes the world from `(v, l)` to
`(v / 2, l + 1)`.

This is the lane's **first proof that steps the walker through a write**,
and it is where the two previous inches meet:

* `go_run` (§G10's seam) steps `lookupLocal`, `loadAddr` and `storeLocal`
  — the three §G8 called unprovable;
* `wRead_wStore_other` (§G8's frame predicate) shows that **writing `len`
  leaves `n` alone**, which is the whole reason the invariant carries
  `an ≠ al`. That distinctness is not bookkeeping: without it the second
  statement could not be shown to read what the first did not touch.

**`cond_eval`**: `n != 0` reads `n`, compares to zero, and leaves the
world untouched.

Both stated against an explicit `Inv` structure — distinct addresses,
and each holding the value the mathematics says it should. Both take
fuel as `4 ≤ f` / `2 ≤ f` rather than a literal successor pattern, so the
induction can apply them without destructuring first.

Axioms: `propext`, `Quot.sound`, `Classical.choice` at worst. No `sorry`.

### THE BLOCKER MOVED — and this one is narrow

§G8's blocker was *"cannot step the walker at all."* That is gone. The new
one is sharper and worth naming exactly, because it is a Lean fact rather
than a design gap:

> **`simp` will not rewrite inside a DEPENDENT MATCH DISCRIMINANT.**

`execLoop`'s reduced form is

    match pure false w with
    | .error …
    | .ok (.error …)
    | .ok (.ok a, w') => if a = false then … else …

and `run_pure` fires on `pure false w` **in isolation** — checked, it
closes by `rw` — but not in that position, because the branches' types
depend on the scrutinee. Three separate reduction strategies (`simp only`
with the full `go_run` set, staged rewriting, and `rfl`) all leave the
same goal.

The fixes are known and findable: a match-congruence lemma for
`execLoop`'s scrutinee, or binding the condition into a `let` before the
match so the discriminant is a variable. **That is one lemma or one
definitional tweak, not a campaign.**

### Why this is reported as a partial rather than pushed further

The alternative on offer was to keep grinding at a reduction detail with
the session's remaining budget, and land either a `sorry` or a
half-finished proof carried across a boundary. The lane has now twice
found that **naming the blocker precisely is worth more than one more
attempt** — §G8 named its blocker, §G10 cleared it in one file, and this
entry names a strictly smaller one. The trajectory is the argument:

| entry | blocker | size |
| --- | --- | --- |
| §G8 | the monad stack does not reduce at all | a lemma SET (`py_simp`'s analogue) |
| §G10 | — cleared by `Obs.lean`, 10 rows | — |
| §G11 | one dependent-match discriminant will not rewrite | **one congruence lemma** |

### Triad

**Tenure GREEN**: `lake build` exit 0 (scoped to `LeanModels.Go` and the
exemplar), `docs_check` **91/91**, `diff_test` **1,427 cases, 0 failed**
(1,311 matched, 116 whitelisted), `script_corpus` **65 scripts, 0
failed**. Lock was free — acquired in **0 s**, held **62 s**, the
lane's fastest tenure yet and the first with no queue at all.

`fallthrough` deferred (4.0%); MM-oracle untouched.

---

## G12 — THE LOOP INDUCTION CLOSES: `len = l + bitLenSpec v`, proved (2026-08-23)

§G11's blocker was *"`simp` will not rewrite inside a dependent match
discriminant."* It is cleared, and the loop's correctness is a theorem.

### THE CONGRUENCE — and the trick is to never touch the scrutinee

`LeanModels/Go/Obs.lean` §1b, three rows beside the seam. **The answer is
not a congruence over the scrutinee**, which would still leave a match:
it is to rewrite the WHOLE bind from a proved equation about what its
head DOES.

    run_bind_ok    (h : x w = .ok (.ok a, w')) : (x >>= f) w = f a w'
    run_bind_loud  (h : x w = .error l)        : (x >>= f) w = .error l
    run_bind_panic (h : x w = .ok (.error e, w')) : (x >>= f) w = .ok (.error e, w')

Three because the stack has three outcomes, and the split is the covenant
again — loud stops everything, a panic propagates carrying its world,
only a value continues. **They live beside the seam, not in the exemplar
that needed them first, because they are reusable at every loop and every
`do` block this tier will ever prove about.** The Lean fact they exist for
is named in a comment above them.

Per the ruling, the lemma was preferred over let-binding `execLoop`'s
scrutinee: **the definition stays untouched.**

### THE INDUCTION

`loop_computes` — strong induction on `v`; each turn is `cond_eval` to
test, `body_step` to advance, the hypothesis at `v / 2`. Two facts the
proof needed that are worth recording:

* `dsimp only` for the **iota** step. After `run_bind_ok hw1` the goal is
  `match Flow.normal with …` — a match on a literal constructor, which
  `simp only` will not reduce but `dsimp only` will. A second, smaller
  instance of the same family of obstacle.
* The **`asBool` prefix is its own bind.** `execLoop`'s head is
  `evalExpr … >>= fun v => asBool v >>= …`, not `(evalExpr >>= asBool) >>= …`
  — discovered by tracing the goal rather than assumed, after a `show`
  built on the assumed shape failed.

### THE FINAL CLAIM, in one table

| layer | statement | status |
| --- | --- | --- |
| **spec** | `bitLenSpec_lt` — `n < 2 ^ bitLenSpec n` | **PROVED** |
| **spec** | `bitLenSpec_le` — `0 < n → 2 ^ (k-1) ≤ n` | **PROVED** |
| **spec** | `bitLenSpec_le_64` — a bit length never exceeds the width | **PROVED** |
| **bridge** | `shr_one_is_halving` — the interpreter's `>>= 1` IS the spec's `/ 2` | **PROVED** |
| **interp** | `cond_eval` — `n != 0` reads `n`, world untouched | **PROVED** |
| **interp** | `body_step` — one turn: `(v, l) → (v/2, l+1)` | **PROVED** |
| **interp** | **`loop_computes` — the loop leaves `len = l + bitLenSpec v`** | **PROVED** |
| differential | 35 oracle rows (what `gc` printed) | checked |
| differential | 35 spec rows (`bitLen n = bitLenSpec n`) | checked |
| **owed** | the prologue/epilogue — `bindParams`, `var len = 0`, `return len` — composing the loop theorem up to `callFunction` | **not proved** |

**The first two bracket the mathematics, the bridge joins it to the
interpreter's arithmetic, and the induction carries it through the
loop's mutation. What is still checked rather than proved is the
function's frame around the loop** — three statements, each of the shape
`body_step` already handles, and the honest remaining step.

So the exemplar's claim is now precise: *the loop is correct, proved; the
function is correct, checked on 35 inputs against two independent
standards.* §G6 wrote that distinction into the file before it could be
closed, and closing half of it did not change what the other half says.

### The blocker ladder, complete

| entry | blocker | size |
| --- | --- | --- |
| §G8 | the monad stack does not reduce at all | a lemma SET |
| §G10 | — cleared by `Obs.lean`'s seam, 10 rows | — |
| §G11 | a dependent-match discriminant will not rewrite | one congruence |
| §G12 | — cleared by `run_bind_ok` and friends, 3 rows | — |

Axioms: `propext`, `Quot.sound`, `Classical.choice` at worst;
`run_bind_ok` depends on **`propext` alone**. No `sorry`, no
`native_decide`, in either file.

### Triad

**Tenure GREEN**: `lake build` exit 0 (scoped to `LeanModels.Go`,
`LeanModels.Go.Obs` and the exemplar), `docs_check` **91/91**,
`diff_test` **1,427 cases, 0 failed** (1,311 matched, 116 whitelisted),
`script_corpus` **65 scripts, 0 failed**. Held the machine **88 s**.

`fallthrough` deferred (4.0%); MM-oracle untouched.

---

## G13 — THE EXEMPLAR IS COMPLETE: the FUNCTION is correct, proved (2026-08-23)

§G12 proved the loop. This carries it through the function's frame, and
the claim changes accordingly.

### THE COMPOSITION — one inch, as the table predicted

§G12's table said each remaining statement was `body_step`-shaped. It
was, and the inch is four small lemmas plus the wrapper:

* `bindParams_ok` — the parameter lands at address 0;
* `declare_ok` — `var len = 0` lands at address 1, giving `setupW`;
* `for_step` — the `for` statement: **no init, so the loop-variable set
  is empty and the version branch is a no-op here**, and the loop's
  locals-restore is the identity on this frame;
* `ret_ok` — `return len` reads `len` and returns it;
* `bitLen_correct` — the four composed through `callFunction`.

**And one generalisation the composition forced, which is the better
design anyway:** `body_step`, `cond_eval` and `loop_computes` were stated
with `[]` as the program table, because the loop calls nothing.
`callFunction` passes the real table, so they are now stated over an
arbitrary `P : FuncTable`. The loop genuinely does not care, and now says
so.

`run_bind_ok` did every step. `dsimp only` did the iota reductions
between them — the same second-order obstacle §G12 recorded, hit twice
more and dispatched the same way.

### THE FINAL CLAIM

| layer | statement | status |
| --- | --- | --- |
| spec | `bitLenSpec_lt` — `n < 2 ^ bitLenSpec n` | **PROVED** |
| spec | `bitLenSpec_le` — `0 < n → 2 ^ (k-1) ≤ n` | **PROVED** |
| spec | `bitLenSpec_le_64` — never exceeds the width | **PROVED** |
| bridge | `shr_one_is_halving` — the interpreter's `>>= 1` IS the spec's `/ 2` | **PROVED** |
| interp | `cond_eval`, `body_step` — the loop's test and one turn | **PROVED** |
| interp | `loop_computes` — the loop leaves `len = l + bitLenSpec v` | **PROVED** |
| interp | `bindParams_ok`, `declare_ok`, `for_step`, `ret_ok` — the frame | **PROVED** |
| **whole** | **`bitLen_correct` — `callFunction … "bitLen" [v]` returns `bitLenSpec v`, for every `v < 2⁶⁴`** | **PROVED** |
| **whole** | `bitLen_eq_spec` — the same, in the form the guards call | **PROVED** |
| corroboration | 35 spec rows | now **instances of a theorem** |
| corroboration | 35 oracle rows — what `gc` actually printed | **keep full weight** |

**The claim is now: the FUNCTION is correct, proved.** §G6 wrote the
distinction *"model and toolchain agree"* versus *"`bitLen` is correct"*
into the file before either was closed; both are now closed, and the file
says which is which.

**The 35 oracle rows are NOT demoted, and that is deliberate.** They are
the only thing tying the model to what the compiled function actually
printed. `bitLen_correct` proves the model computes `bitLenSpec`; it
cannot prove `gc` does. Only the oracle rows carry that, and no theorem
about the model can replace them. The 35 SPEC rows are demoted, because
they are now instances of `bitLen_eq_spec`.

22 theorems in the exemplar. Axioms `propext`, `Quot.sound`,
`Classical.choice` at worst. No `sorry`, no `native_decide`.

### NEXT INCH, censused from the selector worklist

§G8's brief said the cheap tier's value is *"a better refusal plus a
ranked worklist"*. Here is the worklist paying out. Of the 438 stdlib
packages called, ranked by call volume, the top of the list splits by
whether this tier could ever model them:

| package | calls | modellable? |
| --- | ---: | --- |
| `fmt` | 10,567 | yes, but it is the **verb mini-language** — its own spec (§5.4's `printf` problem) |
| `unsafe` | 8,966 | **never** — it is the escape hatch |
| `strings` | 6,042 | yes — pure functions, but needs the string tier |
| **`math/bits`** | **3,936** | **yes, and it is the closest** |
| `os`, `time`, `C` | 3,900 / 1,835 / 1,833 | environment, clock, cgo — all outside |

**`math/bits` is the first package on the list this tier could actually
execute**: 49 exported functions, **26 with a plain integer signature**,
no state, no I/O. And `bits.Len` is *the same function as the exemplar*.

**But it is blocked on exactly one thing, and the census names it: eight
of those functions are TABLE-DRIVEN** (`len8tab`, `ntz8tab`, `pop8tab`) —
they need array types and indexing, which are §G6's #2 and #3 blockers
(`ArrayType` 48.0%, `IndexExpr` 28.3% of rung-1-reachable files) and are
in the vocabulary but not stepped.

**And that is why this exemplar was reachable at all.** `bigmod.bitLen`'s
own comment says it exists because *"bits.Len and bits.LeadingZeros use a
lookup table for the low-order bits on some architectures"* — the crypto
code hand-rolls the loop **to avoid the table**. The census picked the one
function in this neighbourhood that does not need the construct the tier
lacks, without knowing that was why. Next inch: **array types and
indexing**, which unlocks `math/bits` and is the largest remaining
sequential blocker.

### Triad

**Tenure GREEN**: `lake build` exit 0 (scoped to `LeanModels.Go` and the
exemplar), `docs_check` **91/91**, `diff_test` **1,427 cases, 0 failed**
(1,311 matched, 116 whitelisted), `script_corpus` **65 scripts, 0
failed**. Held the machine **58 s**.

`fallthrough` deferred (4.0%); MM-oracle untouched.

---

## G14 — THE ARRAY RUNG IS NOT THE ARRAY RUNG: the tables are STRINGS, and a live mis-bucketing fell out (2026-08-23)

Census-first, and the census refuted the inch's premise — including
**§G13's own sentence**, which said `math/bits`' table functions need
*"array types and indexing"*. They do not.

### WHAT THE TABLES ACTUALLY ARE

    const len8tab = "" +
        "\x00\x01\x02\x02\x03\x03\x03\x03…"

All four — `len8tab`, `ntz8tab`, `pop8tab`, `rev8tab` — are **untyped
string constants**, and the acceptance case is string indexing:

    func Len8(x uint8) int   { return int(len8tab[x]) }
    func Reverse8(x uint8) uint8 { return rev8tab[x] }

`len8tab[x]` indexes a STRING and yields a byte. `Reverse8` returns it
directly — no conversion needed, because indexing a string already gives
`uint8`. So the rung the acceptance case actually needs is **string
indexing plus type conversions**, and **neither arrays nor slices appear
in it at all.**

This is the second time the corpus has corrected a rung's definition
before a line of it was written, and the first time it corrected an entry
this lane had already published.

### THE ARRAY/SLICE SPLIT, censused anyway — because the rung will come

`[N]T` and `[]T` are the SAME `go/ast` node kind; only `Len` separates
them, so the 48.0% figure §G6 reported for `ArrayType` was two different
semantic objects added together. Split:

| shape | n | share |
| --- | ---: | ---: |
| slice `[]T` | **46,188** | **85.4%** |
| fixed array `[N]T` | 7,923 | 14.6% |

**Slices outnumber fixed arrays 6:1.** The coordinator's sizing question
was whether the tier might skip slice semantics because the tables are
fixed-size; the answer is that the tables are neither, and when the rung
does come, **slices are the weight and fixed arrays are the tail** —
the opposite of the assumption worth checking.

### AND THE CENSUS FOUND A LIVE DEFECT

`int(x)` parses as a `CallExpr` on an `Ident` — syntactically identical
to a call to a function named `int`. The walker therefore refused every
conversion as **`environment`**, verified by running it:

    #eval convRefusal   -- some "environment"    (before)
    #eval convRefusal   -- some "unsupported"    (after)

That is a §5.2 mis-bucketing, and not a cosmetic one: `environment`
retires by **widening the modelled slice**, `unsupported` by **climbing a
rung**. They are different work on different schedules, and §5.2 requires
them reported apart.

**Measured: 51,255 of the standard library's plain-identifier calls are
conversions to a predeclared type — 26.3% of them, 9.7% of all calls.**
Every one was in the wrong bucket. The predeclared type names are the one
case a tier can separate without `go/types`, so the fix is a 21-name list
and one arm; it is landed, with a **paired guard** — one conversion, one
genuinely-undefined function — so a regression in either direction shows.

This also sharpens §G8's brief: the ranked worklist it produced was a
worklist of `environment` refusals, and **a quarter of what would have
been on it was never an environment problem at all.**

### THE RUNG, REDEFINED

| what | why |
| --- | --- |
| **string indexing** (`s[i]` → byte) | the acceptance case *is* this |
| **type conversions** (`int(…)`, `uint8(…)`) | the other half of `Len8`; 51,255 sites; now correctly bucketed |
| ~~fixed arrays~~ | not needed by the acceptance case; 14.6% of `ArrayType` |
| ~~slices~~ | not needed either; 85.4%, and the real weight when the rung comes |

Declaring only what the rung executes is this lane's own vocabulary law
(§G6: the bitwise operators were left undeclared for exactly this
reason), and the census is what keeps it honest.

### Triad

**Tenure GREEN**: `lake build` exit 0, `docs_check` **91/91**,
`diff_test` **1,427 cases, 0 failed** (1,311 matched, 116 whitelisted),
`script_corpus` **65 scripts, 0 failed**. Held the machine **59 s**.
80 `#guard`s in the exemplar.

`fallthrough` deferred (4.0%); MM-oracle untouched.
