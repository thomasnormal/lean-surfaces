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

