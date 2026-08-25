# The Go lane's backlog

Per-lane file per `docs/family-architecture.md` §9.5. **Appended only by the
Go lane.** Ids are `YYYY-MM-DD-go-<n>` and need no reservation, because the
lane name makes them unique. Entries newest-last.
The founding charter is `docs/go-charter.md`; the founding landing is
`docs/backlog.md` §L76.

---

### SPEC COVERAGE — the completion metric (standing; updated every landing)

The tier's goal is COMPLETION, and this is the number that measures it:
how many real stdlib files the walker steps **entirely**. Coverage is
CONJUNCTIVE (§G1) — a file counts only when EVERY construct it uses is
modelled — so this is a floor on completeness, never a score.

Reproduce it, do not quote it:

    harness/go/census.sh --reach $(go env GOROOT)/src

The vocabulary it measures against is transcribed from
`LeanModels/Go/Stmt.lean` and **must be widened in the same commit that
widens the walker** (§G19, after the previous table proved unreproducible).

| rung | sha | all of `$GOROOT/src` | the LIBRARY only |
| --- | --- | ---: | ---: |
| §G16 re-rank | — | *withdrawn — unreproducible (§G19)* | — |
| §G19 range / slice family | `5b3602f` | 604 / 3,803 (15.9%) | — |
| §G20 fixed arrays `[N]T` | `da9a7bc` | 680 / 3,803 (17.9%) | 587 / 2,743 (21.4%) |
| §G22 rung E1 (`pkg.F` + `math/bits`) | `4a9f9ec` | 680 / 3,803 (17.9%) | 587 / 2,743 (21.4%) |
| §G23 multi-value returns | `9a6d6ad` | 680 / 3,803 (17.9%) | 587 / 2,743 (21.4%) |
| §G24 `math/bits` complete + constants | `eb1e8b0` | 687 / 3,803 (18.1%) | 594 / 2,743 (21.7%) |
| §G25 variadics | `9b2129e` | ~~739 / 3,803~~ *overstated, see §G27* | ~~644 / 2,743~~ |
| §G27 correction (same tree; no rung) | `fa625f5` | 717 / 3,803 (18.9%) | 629 / 2,743 (22.9%) |
| §G28 bundle (methods, strcat, string slice, `strconv`) | `5fca2f5` | **765 / 3,803 (20.1%)** | **657 / 2,743 (24.0%)** |

E1 moved the mechanism, not the metric: **+0 files** (§G22). The table is
unchanged on purpose — a mechanism rung that unlocks nothing must not be
allowed to look like progress here.

*(A landing's own sha cannot appear in the commit that creates it — a
commit does not contain its own hash, and amending to insert it changes
it again. So each rung's sha lands in the FOLLOWING commit, which is how
§G19's and §G20's rows were filled. Noted here because the first attempt
at this row cited a sha that the amend had already destroyed.)*

**Two denominators, because the choice is a real one and it moves the
number by 3.5 points.** `$GOROOT/src` includes `cmd/` — 1,060 files, 28%
of the corpus — which is the Go *toolchain*: one large program's
internals, not the language's subject matter. It is legitimate Go and the
tier must eventually step it, so the first column stays. But it badly
skews *ranking*: with `cmd/` in, the most-selected packages are `ir`,
`obj`, `ssa` and `base` — `cmd/compile`'s own guts. Rank over the library
(§G21).

**This metric measures SYNTACTIC coverage — kind-set containment — and
that is an upper bound, not executability.** For every construct modelled
so far the two coincide, because the walker implements each kind's
semantics. They will NOT coincide for selectors: knowing `fmt.Println` is
a package call is not being able to run it (§G8; quantified in §G21,
where the naive figure overstates by 2.5×). So a syntactic-only win must
never be banked in this table.

Ceiling at this vocabulary: **3,767 (99.1%)** — what the walker would
reach if every frontier construct were modelled. The gap between 680 and
3,767 is the remaining work; §G21 prices which part is worth taking.

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
## 2026-08-22-softfloat-4 — INBOUND FROM THE SOFTFLOAT LANE: Go lane's to triage

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

---

## G15 — RUNG 4: a Go string is BYTES, and a conversion is its own node (2026-08-23)

The rung §G14 redefined, built. The census kept correcting things on the
way in, so the entry is mostly corrections.

### THE CENSUS: `rev8tab` decides the value model

`Len8`'s table holds only 0..8 — it would fit any string representation.
**`rev8tab` holds 128 bytes ≥ 0x80 of its 256** (measured through
`bits.Reverse8` itself, not by parsing the source, after a first parse
miscounted the length as 240).

And a Lean `Char` at code point 200 is **two** bytes in UTF-8 — measured,
`(String.singleton c).utf8ByteSize = 2`. So a Lean `String` cannot hold
that table with `len` 256 and `s[i]` byte-exact.

**`GoVal.stringV (s : String)` was therefore wrong**, and the
specification says so directly: *"a string value is a (possibly empty)
sequence of bytes"*, with `s[i]` yielding a **byte**. It is now
`stringV (bytes : List UInt8)`. Blast radius was 7 sites — the census
checked before the change, and it is why the change was cheap.

**Taking `Reverse8` now rather than deferring it is the point.** `Len8`
alone would have passed under the wrong representation, and the value
model would have been rebuilt after this rung was built on it.

### A SECOND MODELLING ERROR, found by the cost

Once strings were bytes, every run-time panic forced `String.toUTF8`
through the kernel and four `#guard`s timed out. Chasing that surfaced a
faithfulness bug: **Go's run-time panics do not carry a string.** They
carry a value implementing `runtime.Error`. `GoVal` gained
`runtimeErrorV`, which is both the faithful shape and the cheap one — the
performance symptom was pointing at a correctness defect.

### AND A THIRD — the conversion node

§G14 landed conversions as a branch inside `evalExpr`'s `.call` arm.
Measured, that was too expensive: **0 proof timeouts without the branch, 4
with it**, and moving it onto the lookup's `none` path did not recover
them. `set_option maxHeartbeats` did not take effect either.

**The fix was the design, not the budget.** A conversion IS a different
construct — Go's grammar merely spells it like a call, and `go/ast`
conflates them — so it is now `Expr.convert`, its own node, emitted by the
frontend from the predeclared-name list. That is what
`docs/go-charter.md` §7.3 already rules for everything type-dependent: the
frontend disambiguates, the walker steps. `evalExpr`'s `.call` arm is
thin again, no heartbeat bump was needed, and the model says what it
means.

*This is the third time this rung a performance symptom turned out to be
a modelling question.*

### THE ACCEPTANCE CASE — `Examples/go/bits8/`

    func Len8(x uint8) int       { return int(len8tab[x]) }
    func Reverse8(x uint8) uint8 { return rev8tab[x] }

vendored from `src/math/bits/bits.go`, and transcribed as
`int(len8tab[x])` = a **conversion of a string index** — exactly the two
constructs this rung added.

**Both checked exhaustively over all 256 inputs, one guard each**, against
two different standards:

| function | standard | why it is independent |
| --- | --- | --- |
| `Len8` | **`bitLenSpec`** — §G13's PROVED spec | one side is a table lookup, the other a proved recursive specification, derived by different routes |
| `Reverse8` | what `gc` printed | no proved spec exists, so the compiler is the standard |

`Len8` against `bitLenSpec` is the nicer half: **the theorem proved for
the crypto lane's hand-rolled loop now predicts the standard library's
table-driven function**, and the two agree on every input.

Three named high-byte rows (`Reverse8 1 = 128`, `255 = 255`, `129 = 129`)
sit beside the sweep so a representation that lost the high bit fails by
name and not only in bulk. Non-vacuity RUN on both: flipping the high-byte
row and breaking the exhaustive sweep each make Lean report it.

### Also in this rung

String indexing yields a **byte** (`uint8`), and an out-of-range index is
a **run-time panic** — a defined outcome, in ρ, never `undefined`.

### Triad

**Tenure GREEN**: `lake build` exit 0, `docs_check` **91/91**,
`diff_test` **1,427 cases, 0 failed** (1,311 matched, 116 whitelisted),
`script_corpus` **65 scripts, 0 failed**. Held the machine **62 s**.

`fallthrough` deferred (4.0%); arrays and slices still deferred with
§G14's split (slices 85.4%); MM-oracle untouched.

---

## G16 — THE RE-RANK: the walker has doubled its reach, and the next rung is ONE family (2026-08-23)

Census only, no semantics. Re-ranked with conversions correctly bucketed
(§G14) and strings-as-bytes landed (§G15).

### WHERE THE WALKER IS

| measure | files | of |
| --- | ---: | ---: |
| standard library | 5,419 | — |
| rung-1 INGESTER reach | 3,084 | 56.9% of stdlib |
| **WALKER steps entirely** | **1,289** | **41.8% of reachable** |

**633 → 1,289: rungs 3 and 4 doubled it.** That is calls, conversions and
string indexing, and it is the first time the walker's number has moved by
more than a rounding.

### WHAT IT STILL REFUSES, re-ranked

| construct | files | share of reachable |
| --- | ---: | ---: |
| `ArrayType` | 1,479 | 48.0% |
| `RangeStmt` | 676 | 21.9% |
| `SliceExpr` | 541 | 17.5% |
| `FuncLit` | 442 | 14.3% |
| `SwitchStmt` / `CaseClause` | 432 / 430 | 14.0% |
| `GoStmt`, `ChanType`, `SendStmt`, `SelectStmt`, `CommClause` | 26 … 9 | ≤0.8% |

### THE FINDING: the top three are ONE FAMILY, and it is conjunctive again

`ArrayType`, `SliceExpr` and `RangeStmt` are not three rungs. They are
slices — `[]T`, `a[i:j]`, and `for … range` over one — and measured as
unlocks they behave exactly like §G1's bundles:

| added | files reached | delta |
| --- | ---: | ---: |
| baseline | 1,289 | — |
| `ArrayType` alone | 1,817 | +528 |
| `SliceExpr` alone | 1,316 | **+27** |
| `RangeStmt` alone | 1,318 | **+29** |
| **all three** | **2,308 (74.8%)** | **+1,019** |

**Sum of the parts is 584; the whole is 1,019 — 1.7×.** Ship any one and
almost nothing moves; ship the family and reach goes 41.8% → 74.8%. This
is the third independent reproduction of the conjunctive law in this lane
(§G1's bundles, §G4's switch family, now slices), and the first where the
parts are individually near-worthless in the *single digits*.

**Everything else is small, and two are ZERO:**

| cluster | delta |
| --- | ---: |
| `SwitchStmt` + `CaseClause` | +141 |
| `FuncLit` | +56 |
| `MapType` | **+0** |
| interfaces (`InterfaceType` + `TypeAssertExpr` + `TypeSwitchStmt`) | **+0** |

A `+0` means **no rung-1-reachable file is blocked ONLY by that
construct** — every file using a map or an interface also uses something
else the walker lacks. So maps and interfaces cannot be a next rung at any
price; they are strictly downstream of slices.

### THE STRINGS PACKAGE DOES NOT START PAYING — and the reason is precise

The question was whether §G15's strings-as-bytes makes the `strings`
package (6,042 calls) reachable. **It does not, and the two things are
unrelated:** `strings.Index(…)` is a **selector call**, and §G8 measured
selector calls at 52.4% of all call sites and ruled them `go/types` work.
The blocker is **resolving `strings` to a package**, not representing its
values. Landing the byte representation changed what a string IS; it did
not change what `pkg.F` means.

That distinction is worth keeping because the two look adjacent and are
not: the value model was this lane's to fix, and the selector resolution
is the extractor's — §G8's brief, ratified, still unstarted.

### NEXT RUNG, sized by the census

**Slices, as one family**: `[]T`, `a[i:j]`, and `range` over a slice.
Reach 41.8% → 74.8%. Fixed arrays `[N]T` are **14.6%** of `ArrayType`
(§G14) and are NOT part of it — declare only what executes.

The acceptance case should be picked the way §G13's was: a real function
the census surfaces, chosen so it can FAIL under a wrong model — §G15's
lesson that `Reverse8`, not `Len8`, decided the value model.

`fallthrough` deferred (4.0%); maps and interfaces measured at +0 and
strictly downstream; MM-oracle untouched.

---

## G17 — THE SLICE RUNG'S ACCEPTANCE PICK: the discriminator lives in the CALL (2026-08-23)

Census only. The brief: find a small vendored function exercising **both**
aliasing and the len/cap distinction, the way `rev8tab` decided strings.

### THE SEARCH

Swept every non-generic, non-method stdlib function for ones using a slice
expression together with a write through an index, small and free of
constructs beyond this rung. **60 candidates.** Tightened to require a
MIDDLE slice `a[i:j]` — the only place `cap` and `len` come apart, since a
tail slice `a[i:]` has `cap == len` — and it collapses to **8**, every one
of which needs interfaces, `clear`, `append`, or range-over-struct-slice.

**So no small vendored function exercises both.** That is the census
result, and the interesting part is what follows from it.

### THE PICK — `runtime.itoa`, and the discriminator is the CALL SITE

    func itoa(buf []byte, val uint64) []byte {
        i := len(buf) - 1
        for val >= 10 { buf[i] = byte(val%10 + '0'); i--; val /= 10 }
        buf[i] = byte(val + '0')
        return buf[i:]
    }

`src/runtime/error.go`, 57 nodes, no external calls. It needs `len`, an
index write, a tail slice, a `byte` conversion (rung 4) and a loop — this
rung plus what is already built.

**Called on a MIDDLE slice, it discriminates both**, measured against
`gc`:

    mid := base[2:6]          len=4 cap=6      -- cap and len apart
    out := itoa(mid, 42)
    RET  "42"   len=2 cap=4                    -- len != cap in the RESULT
    BASE "....42.."                            -- writes landed in base
    out[0]='X'  ->  BASE "....X2.."            -- ALIASING, decisive
    out[:cap(out)] = "X2.."  len=4             -- reaches PAST mid's end

**The finding: a discriminating acceptance case does not have to be a
discriminating FUNCTION.** The corpus had none small enough; the vendored
function plus a chosen call site has the property, and the call site is
still not a pet program — it is how a caller in the corpus would use it.
That generalises §G15's rule: *take the case that can fail under a wrong
model* — and the case is (function, argument), not the function alone.

### WHY EACH ROW KILLS THE NAIVE MODEL

A slice as a list copy passes more than it should, which is the trap:

| row | naive list-copy model |
| --- | --- |
| `RET "42"` | **PASSES** — the return value is right |
| `BASE "....42.."` | fails — the caller's array never saw the writes |
| `out[0]='X'` → `BASE` | fails — no shared backing array |
| `out[:cap(out)]` reaching past `mid` | **cannot even be expressed** — a copy has no cap beyond its length |

The last row is the sharpest: a value that reaches *beyond its own length
into a longer array* has no representation in a copy model. So the value
model is decided up front, as the brief expected — **backing array +
offset + len + cap**, not a list.

### THE RUNG, sized

* `[]T`, `a[i:j]`, index read/write through a slice, `len`, `cap`;
* **`range` over a slice reuses `execLoop`** — the machinery the `bitLen`
  induction is proved about — rather than forking it;
* fixed arrays `[N]T` excluded (14.6% of `ArrayType`, §G14);
* `append` NOT declared: `itoa` does not use it, and its growth rule is
  its own question. Declare only what the rung executes.

Acceptance: `itoa` on a middle slice, all four rows above, oracle columns
`printf`-ed from `gc` as always.

`fallthrough` deferred (4.0%); maps and interfaces at +0 and strictly
downstream (§G16 — **the "at any price" half of that is retracted in
§G19**); MM-oracle untouched.

---

## G18 — THE SLICE RUNG: a header, not a list, and the row a copy model cannot state (2026-08-23)

Built as §G17 sized it.

### THE VALUE MODEL, decided up front

    | arrayV (elems : List GoVal)                        -- the backing object
    | sliceV (backing : Addr) (off len cap : Nat)        -- the header

A slice is a **header into a backing array in the store**, which is what
lets two slices share one. The old `sliceV (elems : List GoVal)` had no
consumers, so replacing it cost nothing — checked before changing it.

### THE ACCEPTANCE CASE — `runtime.itoa` on a MIDDLE slice

`Examples/go/itoa/`. Vendored verbatim, called as §G17's census
prescribed: `mid := base[2:6]`, len 4, cap 6. Every expected value
`printf`-ed from the compiled function.

| row | what it checks | a list-copy model |
| --- | --- | --- |
| 1 | the return header is `(off 4, len 2, cap 4)` | **PASSES** — the trap |
| 2 | the caller's array reads `"....42.."` | fails |
| 3 | `out[0]='X'` makes it `"....X2.."` | fails |
| 4 | `out[:cap(out)]` is `(off 4, len 4, cap 4)` | **cannot be stated** |

Row 4 is the rule's strongest form: the wrong model does not *fail* it —
a copy has no capacity beyond its own length, so the value that row names
has no representation. **Non-vacuity RUN on rows 3 and 4**: flipping row 3
to claim the write is invisible, and row 4 to the copy model's `cap == len`,
each make Lean report it.

Also guarded: the argument's own `len 4` / `cap 6` — genuinely apart —
and that an out-of-range index is a **run-time panic**, a defined outcome
in ρ, never `undefined`.

### THE FRAME PREDICATES, aliasing-aware

§1.3b frames a write to an ADDRESS. A slice write goes through a header
into a backing array, and **two headers can name the same element**, so
the pair needs its aliasing form. Landed beside the originals:

* `sliceElem_set_alias` — **a write through one slice IS visible through
  an overlapping one** (row 3, as a theorem);
* `sliceElem_set_disjoint` — **and invisible through one that does not
  overlap**;
* `slice_write_other_backing` — across DIFFERENT backing arrays, which
  needs no new proof: backing arrays are store entries keyed by address,
  so it is `wRead_wStore_other` unchanged, recorded so the pair is
  findable as a pair.

The aliasing question turned out to be **entirely `off + i`** — two
headers name the same element exactly when their offset-plus-index sums
agree. So `AliasAt` mentions no header at all; it is arithmetic, which is
what keeps these in the spec half. Both depend on **`propext` alone**.

### What was NOT built, and why

**`range` over a slice.** §G17 sized it into the rung with the note that
it should reuse `execLoop` rather than fork it — but `itoa` does not use
it, and this lane's vocabulary law is *declare only what the rung
executes*. It is the next thing, and the note stands: when it lands it
reuses the loop machinery the `bitLen` induction is proved about.

`append` likewise absent — `itoa` does not use it and its growth rule is
its own question. Fixed arrays `[N]T` still excluded (14.6%, §G14).

### Triad

**Tenure GREEN**: `lake build` exit 0, `docs_check` **91/91**,
`diff_test` **1,427 cases, 0 failed** (1,311 matched, 116 whitelisted),
`script_corpus` **65 scripts, 0 failed**. Held the machine **63 s**.

`fallthrough` deferred (4.0%); maps and interfaces at +0 and strictly
downstream (§G16); MM-oracle untouched.

---

## G19 — RANGE IS NOT A SECOND LOOP; and the census retracts the `+0` law (2026-08-23)

Two halves. The rung is small and closes the slice family. The census is
not small: re-running the reach measurement to check §G16's promise found
that the promise could not be re-run at all, and that one of this lane's
published laws draws an invalid inference.

### THE RUNG: `range` desugars to `for`

`Stmt.rangeS` does not walk. It builds a three-clause `Stmt.forS` and
calls `execStmt` on it:

```
for k := range s   ⟿   for k := 0; k < len(s); k++
for _, v := range s ⟿  … with `v := s[k]` prepended to the body
```

The range expression is evaluated **once** (the spec's wording) and the
resulting header is captured as a literal, which is what makes the
desugaring faithful rather than merely convenient.

Three things come free, and each is a thing not to get wrong twice:

* every iteration runs the `execLoop` the §G15 induction is **proved**
  about — there is no second loop to keep in step;
* the go1.22 per-iteration scoping applies to the range variable without
  a second version branch, because the range variable **is** the init
  statement's variable;
* the fuel story is `forS`'s.

A guard asserts the reuse directly: the range loop and the hand-written
`for` it desugars to must reach the same value **and** the same world. If
`rangeS` ever forks from `execLoop`, that row breaks.

### THE BUG THE DESUGARING ALMOST SHIPPED

The first implementation used the RANGE VARIABLE as the loop counter —
`for i := range s` ⟿ `for i := 0; i < len(s); i++` literally. That is
wrong, and `gc` says so. Body `n++; i = 100` over a 5-element slice:

| | iterations |
| --- | ---: |
| `for i := range s` | **5** |
| `for i := 0; i < len(s); i++` | **1** |

`range` runs the full length however the body maltreats the range
variable; a hand-written `for` does not. The fix is that **the counter
gets a name no Go program can write** (`«range»`) and the range variables
are DECLARED FROM it at the top of each iteration, so an assignment to
them is discarded by the next iteration's declaration — which is exactly
Go's behaviour.

That change also dissolves the version question instead of answering it.
go1.21 shares one `i` across iterations and go1.22 makes it
per-iteration, but the difference is observable only by capturing `i` in
a closure, and `FuncLit` is not in this walker's vocabulary — so
declaring per iteration is correct for both at the constructs this rung
admits, and `rangeS` needs no version branch of its own.

The guard for it is a **constructed** probe rather than a vendored
function, and is labelled so: none of the 41 vendored candidates the
census surfaced assigns to its range variable. A differential fidelity
question with no corpus witness still deserves a row.

### THE ACCEPTANCE: (function, argument), again

`Examples/go/rangeslice/guards.lean`. Two vendored functions, because the
desugaring has two arms and an arm without an acceptance case is an
untested arm:

| form | vendored | why it discriminates |
| --- | --- | --- |
| `for i := range dst` | `strconv.digitZero` | writes through the header |
| `for _, c := range b` | `net.allFF` | reads through the header |

Both are ordinary functions. The discrimination is in the **argument**:
ranging over `s` touches backing cells `off … off+len-1`, and on a slice
whose header is the identity both halves of that sentence are invisible.

The decisive pair is `allFF` at two arguments over **one** backing array
holding a single `0x00` at cell 6:

| call | `gc` | why |
| --- | --- | --- |
| `allFF(b[2:6])` | `true` | the `0x00` is OUTSIDE the window |
| `allFF(b[4:8])` | `false` | the same `0x00` is INSIDE it |

Same code, same array, same length — only `off` differs, and the answer
flips. **No model that drops the header can produce both**, which is the
property `Reverse8` had in §G15 and `out[:cap(out)]` had in §G18.

11 guards. Every expected value `printf`-ed from the compiled functions
(`go1.25.6 darwin/arm64`), never typed by hand (§G13's law). Non-vacuity
**run, not asserted**: five flips — the written array, both halves of the
`allFF` pair, the reuse row, and the empty-window row — each produce 3
errors. The empty window (`len = 0`) is the boundary the desugared
condition must get right before any iteration, and it comes back with the
array untouched.

### THE CENSUS: §G16's reach table could not be re-run

§G16 promised the slice family takes reach 41.8% → 74.8%. Checking it
turned up the first problem before any number: **the reach measurement
left no instrument behind.** The figures were computed ad hoc and the
vocabulary they were computed against was recorded nowhere, so they could
not be re-derived from the repository.

So the measurement is now an instrument — `construct_census.go --reach`
(`go-reach-0.1`) — and it does two things a kind-set TSV cannot:

1. **It splits `ArrayType`.** go/ast spells `[]T` and `[N]T` with the same
   node, distinguished only by `Len == nil`. This tier models slices and
   not fixed arrays, so a census that cannot tell them apart **cannot
   state this tier's reach at all** — and §G16's headline `ArrayType`
   figure (+528) is exactly that conflation.
2. **It keeps the vocabulary as data**, transcribed from `Stmt.lean`, so a
   rung that widens the walker widens the list in the same commit.

Measured over 3,803 non-test stdlib files:

| vocabulary | files | delta |
| --- | ---: | ---: |
| walker baseline | 512 | — |
| `+ SliceExpr` alone | 514 | **+2** |
| `+ RangeStmt` alone | 512 | **+0** |
| `+ ArrayType/slice` alone | 591 | +79 |
| **+ THE FAMILY** | **604** | **+92** |
| family minus `RangeStmt` | 595 | (range is worth **+9** inside it) |
| `+ ArrayType/fixed` too | 680 | +76 |

The conjunctive law reproduces (parts sum to 81; the whole is 92). The
absolute numbers do **not** reproduce §G16's, and the gap is largely
`SelectorExpr`: widening the vocabulary to treat selectors as steppable
moves the baseline from 512 to 1,114, near §G16's 1,289. That is a
measurement counting as steppable exactly what §G8 ruled is `go/types`
work and this walker refuses. **§G16's 41.8% → 74.8% is withdrawn**; the
reproducible figure for the family as landed is 512 → 604 files, and it is
re-runnable by anyone.

### THE LAW THIS RETRACTS: `+0` does not mean "downstream"

§G16 measured `MapType` and interfaces at +0 and concluded they "cannot be
a next rung **at any price**; they are strictly downstream of slices."
That inference is invalid, and the counterexample is in this very rung:

| construct | alone | inside the family |
| --- | ---: | ---: |
| `RangeStmt` | **+0** | **+9** |
| `MapType` | +8 | +14 |
| interfaces | +4 | +7 |

`RangeStmt` measured +0 alone. By the +0 law it was retirable as strictly
downstream — and it is a load-bearing member of the family that just
shipped. **A construct's delta is a function of the current vocabulary,
not a property of the construct.** A +0 against vocabulary `V` says
blocked-with-something-else *at* `V`; it ranks nothing at any future `V′`,
and every one of these deltas grew when `V` widened. The rule survives
only in its weak form — *+0 means not a rung ON ITS OWN, today* — and the
"at any price" clause is withdrawn. Maps and interfaces are not
disqualified; they are merely still small.

This is the second time in three rungs that the corpus corrected this
lane's own published entry (§G13 was the first), and the first time it
corrected a **law** rather than a fact.

### NEXT, by the reproducible measure

**Fixed-size arrays `[N]T`.** At +76 files on top of the family they are
the largest single remaining blocker — larger than switch (+31), maps
(+14), interfaces (+7) and `FuncLit` (+2) **combined**. §G14 ranked them a
14.6%-of-`ArrayType` sliver and §G16 excluded them; the split-aware census
says they are the rung. That they were deferred by the vocabulary law
remains correct — `itoa` and `digitZero` do not execute them — and it is
the census, not the law, that now calls them up.

`fallthrough` still deferred (4.0%). MM-oracle untouched — Thomas's.

### A TOOL DEFECT THIS RUNG HIT, and it is every lane's

`tools/triad.sh --classify --gates` — `--gates` written LAST, with no gate
list after it — **spins forever, silently, burning a core**. Two runs of
this rung were lost to it (10 and 21 minutes) before it was diagnosed.

The cause is three lines of argument parsing:

```
while [ $# -gt 0 ]; do
  case "$1" in
    --gates)      GATES="${2:-}"; shift 2 ;;
```

`${2:-}` tolerates the missing value, but `shift 2` with **one**
positional left fails, shifts NOTHING, and returns non-zero — and with no
`set -e` on that path the `while` re-enters on the same `--gates` forever.
`sample(1)` confirms it: `execute_while_or_until` → `execute_case_command`,
no children, no output, `RN`.

The failure is nasty in a specific way: it produces **zero bytes**, so it
is indistinguishable from a long queue wait, and the lock is never taken,
so the queue-depth diagnostics say nothing is wrong. Every value-taking
flag has the same shape (`--lane`, `--dir`, `--build-target`, `--against`,
`--rss-limit`, …); `--gates` is merely the one a lane is most likely to
write last out of habit. Suggested fix, once per flag:

```
    --gates)  [ $# -ge 2 ] || die "--gates needs a gate list"; GATES="$2"; shift 2 ;;
```

Routed to the QoL lane. Two notes for other lanes meanwhile: write
value-taking flags with their value, never last-and-bare; and a triad that
has printed **nothing** after a minute is not queuing, it is spinning —
`enqueued …` is the first line of a healthy run.

The near-miss worth naming: `--classify` alone completes and prints
`gates green`, but on the **default** gate set (`docs_check`, `diff_test`)
— it does not run `script_corpus`, which this tier's landings do. A run
that lost its `--gates` argument would therefore still go green, with less
coverage than the lane believes it has. The tool warns (`!! DEFAULT
GATES`), and that warning is the thing to read, not skim.

### VERDICT

`tools/triad.sh --lane go --classify --gates 'python3 tools/docs_check.py;
python3 harness/diff_test.py; python3 harness/script_corpus.py'` —
**green**. Build exit **0**. `docs_check` **91/91 marked blocks**.
`diff_test` **1,427 cases, 0 failed** (1,311 matched, 116
whitelisted-unsupported). `script_corpus` **65 scripts, 0 failed**. Held
the machine **66 s**.

`census.sh --compare` re-verified as a gate after this rung modified the
instrument: **exit 0** identical, **exit 5** on drift.

### A REBASE EXCEPTION, discharged by proof rather than by a rerun

The push rebased onto `29f868e`, which touches a `.lean` file — and the
standing law is re-run build + `diff_test` after any rebase that does.
The re-run queued behind the ada lane for 28 minutes, which made it worth
asking whether it was owed at all. It was not, and the test is checkable:

`lakefile.toml` declares exactly two `lean_lib`s, `LeanModels` and
`Examples` (`globs = ["Examples.+"]`). **`docs/` is not a library and not
a default target**, so `docs/*.lean` — there are three — are standalone
files `lake build` never compiles, and nothing imports this one. The
incoming commit therefore cannot change any verdict about this tree.

So the law's sharp form: *re-run after a rebase touching a `.lean` file
that lake actually builds.* The cheap check is whether the path sits under
a declared `lean_lib` root. The queued re-run was cancelled and its ticket
removed — with seven lanes waiting, holding a slot for a verdict that
could be settled by reading `lakefile.toml` is the expensive mistake, not
the safe one.

---

## G20 — FIXED ARRAYS: the value model that needed no new constructor, and the frontier stops being a construct (2026-08-23)

§G19's reproducible census called this rung: `[N]T` at **+76**, larger
than switch, maps, interfaces and `FuncLit` combined. It measured 604 →
**680**, which is +76 **exactly** — the first time this lane predicted a
reach delta and hit it on the nose.

### THE CENSUS, and how it moved the rung off the plan

The sizing note was that copy-by-value is the discriminator: Go arrays
copy where slices alias. That is true, and it is the value model's
decider. It is **not** what the corpus mostly does:

| operation on a local `[N]T` | stdlib uses |
| --- | ---: |
| `a[:]` slice-of-array | **1,911** |
| `&a` address-of-array | 156 |
| bare-identifier COPY (assign / pass / return) | **152** |

`a[:]` outnumbers copying **12.6×**. And in the 76 files the rung
unlocks, 1,407 `[N]T` occurrences yield only 23 possible copies and 12
slice-of-array — the dominant use there is **declaration**: buffers and
struct fields. The six in-reach candidate functions are all trivial
delegating wrappers in `crypto/internal/fips140/aes`, and every one takes
`*[N]byte` — **pointers precisely to avoid copying**. So the proposed
discriminator has no witness among them.

That does not retire the discriminator; it relocates it, exactly as §G17
ruled. Copy-vs-alias decides the VALUE MODEL whether or not the corpus
exercises it, so it belongs in the acceptance — in the CALL.

### THE VALUE MODEL: no new constructor, because addressability does it

A `[N]T` is a value; a slice is a header. The obvious way to get this
wrong is to reuse `sliceV` for arrays, and then `b := a` aliases.

The model needed **no new constructor**, and the reason is worth stating
because it is the second time this tier got a semantic for free from a
structure already present: **`bindLocal` stores a local's value at its
own address.** Therefore

* `b := a` evaluates `a` to an `arrayV` VALUE and binds it at a FRESH
  address — a deep copy, with **no copy code to get wrong**; and
* `a[:]` needs the ADDRESS the array lives at — which is precisely Go's
  rule that only an **addressable** array may be sliced.

So the arm resolves its operand to an `(addr, off, len, cap)` quadruple:
a slice carries one already, an addressable array supplies its own with
`off = 0` and `cap = len = N`, and anything else is refused — which is
also `gc`'s answer. Addressability is not a special case bolted onto the
model; **it is the shape of the implementation**, and the same resolution
serves `a[i] = v`, for the same reason: the write must be visible through
every slice that aliases it.

The one new syntax node is `Expr.arrayLit n zero` — `[N]T`'s zero value.
The size lives in the VALUE, not in a type annotation, because the size
is what `len` reads and what `a[:]`'s capacity comes from.

### THE ACCEPTANCE: `runtime.printuint`, plus the pair both wrong models fail

Vendored verbatim from `src/runtime/print.go` — the direct sibling of
§G18's `runtime.itoa`, which is why the walker needed only `[N]T` itself
to reach it. `gwrite` is the one thing unmodelled, so the transcription
returns `buf[i:]`; the array, the `len(buf)` seed, the decrementing
three-clause loop, the indexed write and the slice-of-array are as
vendored. `printuint` makes the fixed size load-bearing in a way a
buffer usually does not: `i` is seeded from `len(buf)`, so `N` decides
where the digits land and the returned `cap` is `N - i`. Five rows
against `gc`, contents **and** len **and** cap.

But `printuint`'s array never escapes and is never copied, so it cannot
separate a value model from a header model. The discriminator is one
array with two operations:

    var a [4]byte ; a = "wxyz"
    b := a  ; s := a[:] ; b[0] = 'B' ; s[1] = 'S'

| model | `a` afterwards |
| --- | --- |
| **`gc`** | **`"wSyz"`** |
| arrays-are-headers | `"BSyz"` — the copy leaked |
| slices-are-copies | `"wxyz"` — the alias never landed |

**Both wrong models fail the same row, in opposite directions.** That is
strictly better than §G15's `Reverse8` and §G18's `out[:cap(out)]`, each
of which killed one wrong model; this row is a two-sided vice. Flipping
it to either wrong answer produces 3 errors — run, not asserted, along
with four more flips (the copy's own row, `a[1:3]`'s cap 3 → 2, and two
`printuint` rows).

13 guards. Every expected value `printf`-ed from the compiled program
(`go1.25.6 darwin/arm64`), never typed here.

### THE FRONTIER STOPS BEING A CONSTRUCT

Re-running `--reach` with the vocabulary widened in the same commit as
the walker (the rule §G19 set):

| construct | alone |
| --- | ---: |
| **`SelectorExpr`** | **+1,189** |
| `Ellipsis` | +51 |
| `MapType` | +15 |
| `InterfaceType` | +7 |
| `SwitchStmt`, `FuncLit` | +2 each |
| the other nine | +0 |
| ALL of the frontier | +3,087 |

`SelectorExpr` is **23× the next construct**, and it is not a construct
this lane can model: it is §G8's selector-resolution question — telling
`pkg.F` from `x.field` needs `go/types`, and the brief for it has been
ratified and unstarted since §G8.

So the tier's ranking has changed shape. **For the first time the
walker's vocabulary is not the bottleneck** — every remaining construct
is worth at most +51, and one piece of extractor work is worth +1,189.
Adding constructs from here is sharply diminishing; the next real move is
the extractor.

### A SECOND-TIME SLIP, so it gets a rule

The guard count in this entry was written as 11 and is 13: I counted by
eye. §G19 published 13 for a file holding 11, caught the same way. Twice
is a pattern, not a slip, so the rule is the one this lane already
applies to oracle columns (§G13): **the number comes from the file**, via
`grep -c '#guard'`, and is pasted in — never estimated from the section
headings, which do not correspond one-to-one to guards.

Standing: `fallthrough` still deferred (4.0%) and now visibly minor;
maps and interfaces small but NOT disqualified (§G19's retraction);
MM-oracle untouched — Thomas's.

### VERDICT

`tools/triad.sh --lane go --classify --gates 'python3 tools/docs_check.py;
python3 harness/diff_test.py; python3 harness/script_corpus.py'` —
**green**. Build exit **0**. `docs_check` **91/91**. `diff_test` **1,427
cases, 0 failed** (1,311 matched, 116 whitelisted-unsupported).
`script_corpus` **65 scripts, 0 failed**. Queued **7,501 s** behind five
lanes; held the machine **64 s**.

---

## G21 — THE EXTRACTOR TIER, chartered: authorized on a figure that is 2.5× too big, and sized on the one that is not (2026-08-23)

Census only, no implementation — the C tier's founding template, which is
also how this lane's own charter was written.

Thomas's recalibration authorized the `go/types` extractor tier now, on
the strength of §G20's frontier table: `SelectorExpr` at **+1,189**, 23×
the next construct. The authorization stands and this charter accepts it.
**The figure that motivated it does not survive its own census**, and
saying so is the charter's first job, because §G8 predicted this exact
error in advance:

> the honest value of cheap-tier resolution is **a better refusal, not a
> wider reach** … but it is not reach, and **pricing it as reach would be
> the motivated error**.

§G20 priced it as reach. Here is the correction, measured.

### THE SPLIT, and what each half is worth

`SelectorExpr` is two constructs sharing one `go/ast` node, so the census
instrument now splits it the way it splits `ArrayType` (`fileKinds`):

* **`SelectorExpr/pkg`** — the base identifier is an imported name. This
  is resolvable **syntactically**, from the file's own import list, with
  no type checker at all.
* **`SelectorExpr/value`** — `x.f`, `x.M()`, `a.b.M()`. Needs `go/types`.

| | alone |
| --- | ---: |
| `SelectorExpr/pkg` | **+503** |
| `SelectorExpr/value` | +111 |
| both (§G20's undivided figure) | +1,189 |

Parts sum to 614 against a whole of 1,189 — **conjunctive again, 1.9×**,
the fourth independent reproduction in this lane.

The call-site census reproduces §G8's split closely (`pkg.F` 29.5% of
selector calls against §G8's 30.2%; non-package 70.5% against 69.8% — the
gap is `_test.go` files, which §G8 counted and this run does not). So the
shapes agree. What disagrees is the **ranking**: §G8 ranked by call-site
share, which puts methods first at 58.9%. Ranking by REACH inverts it —
the cheap syntactic half is worth 4.5× the expensive one. **Call-site
frequency and file reach are different metrics, and for a completion goal
reach is the one that counts.**

### WHY +503 IS NOT THE PRICE

A file counts as reached only when every construct in it is modelled. For
selectors that is necessary but **not sufficient**: recognising `fmt.Println`
as a package call does not let the walker RUN it — that needs `fmt`'s
semantics. So the executable question is *how many files become steppable
if the top-k packages are actually modelled*, and it was measured.

Two corrections to the naive figure, both of which shrink it:

1. **`cmd/` skews the ranking.** Excluded (see the standing table).
2. **`unsafe` and `C` are never executable** — §G8 named them; they are
   the 1st and 5th most-selected packages, so counting them as modellable
   inflates every row.

Over the library, with those two excluded:

| packages modelled | files stepped | over baseline 587 |
| --- | ---: | ---: |
| top 1 (`bits`) | 594 | +7 |
| top 3 | 654 | +67 |
| top 6 | 659 | +72 |
| top 12 | 691 | +104 |
| top 25 | 719 | +132 |
| **ALL 271** | **790** | **+203** |

**The whole cheap tier is worth +203 executable files, not +503** — the
naive figure overstates by 2.5×, and it takes all 271 packages to collect
even that. §G8's warning was right, and is now a number.

+203 on 587 is still **+35%**, and still the largest single move
available — so the tier is worth building. It is simply not the
"+1,189, 23× everything" that authorized it, and the ladder below is
sized on +203.

Most-selected modellable packages: `bits`(3,737), `syscall`(3,245),
`fmt`(2,396), `abi`(2,355), `reflect`(2,062), `io`(1,748),
`errors`(1,678), `ast`(1,444), `token`(1,413), `strings`(1,154),
`time`(991), `os`(873).

### THE RUNGS

**E1 — `pkg.F` syntactic resolution, plus the first package modelled
end to end.** No `go/types`. The extractor emits a resolved
`(package, function)` on every package-qualified call site from the
import table; the walker gains a callee it can dispatch on, and a refusal
that NAMES the package instead of saying "selector call" — §5.2's
`environment` bucket retiring by widening, exactly as
`docs/family-architecture.md` prescribes.

The first package should be **`math/bits`**, and not because it is the
most-selected (it is, among modellable ones, but by a thin margin over
`syscall`). It is the right bridgehead because **this lane has already
proved theorems about its functions**: `bitLen` is proved correct
(§G15), and `Len8`/`Reverse8` are accepted against the vendored tables.
The rung therefore tests the *mechanism* — resolution, dispatch, a
package boundary — against semantics already established, instead of
debugging both at once. It is worth only +7 files alone, and that is
fine: E1's deliverable is the mechanism, and the +7 is the honest label
on it.

**E2 — `go/types`-backed resolution.** A type checker in the extraction
path: one large, indivisible step (§G8). It buys `x.M()` and chained
receivers together. Sized only after E1, because E1's refusal worklist —
438 packages ranked by frequency, which E1 makes machine-readable — is
what tells us which types actually need resolving.

**E3 — methods.** Receivers, method sets, and the value/pointer
distinction. Downstream of E2 by construction.

Extractor and walker rungs **alternate as the census prices them**, per
the recalibration. On today's numbers the walker's own frontier is spent
— every remaining construct is worth ≤ +51 — so E1 is next.

### ACCEPTANCE DISCIPLINE — unchanged, and it transfers

The extractor tier inherits the walker's, because none of it is
walker-specific: **(function, argument)** chosen so a wrong model FAILS a
row; every oracle value `printf`-ed from `gc` and never typed by hand
(§G13); **non-vacuity flips RUN, not asserted**; vendored functions
verbatim with their licence; and the vocabulary law — declare only what
the rung executes.

One addition the tier needs: a resolution has a **wrong answer**, not
just a missing one. `pkg.F` where `pkg` is shadowed by a local variable
is a value selector wearing a package's name, and the import-name
heuristic gets it wrong silently. E1's acceptance must therefore include
a **shadowing row** — the case the cheap resolution is most likely to
misread — and the instrument's own `importNames` already documents that
it is a heuristic and which direction it errs in.

MM-oracle untouched — Thomas's. `fallthrough` deferred (4.0%).

---

## G22 — RUNG E1: the mechanism works, and it is worth +0 files (2026-08-23)

E1 as chartered: `pkg.F` resolution in the extractor, dispatch in the
walker, `math/bits` end to end. Both halves are built and gated. **Its
reach is +0**, the charter's own "+7" estimate was optimistic, and this
entry leads with that because §G21 spent its length on exactly this
failure mode.

### THE DIVISION OF LABOUR

* **The extractor resolves.** `bits.Len64(x)` becomes
  `Expr.callPkg "math/bits" "Len64" [x]` from the file's own import table.
  No `go/types`.
* **The walker dispatches.** It never parses a package name.

`callPkg` is its own node for the reason `convert` is (§G14): a decision
the frontend makes once must not be re-made inline at every evaluation.

### THE SHADOWING GATE — a fifth refusal-correctness shape

Every earlier refusal in this lane was an ABSENCE. A resolution can be
**wrong**: `bits` may be a local shadowing the import, and the census
found **484 such binding sites across 198 standard-library files** —
`local "hash" shadows import "hash"`, `local "crc32" shadows import
"hash/crc32"`.

`construct_census.go --resolve` carries a **two-sided** battery, because
both failure directions are real:

| direction | the mistake | rows |
| --- | --- | --- |
| reckless | resolve a SHADOWED use — a wrong answer | 4 |
| timid | refuse an unshadowed use — lost reach | 2 |

The timid direction is the one a naive fix causes: Go's `:=` binds only
from its declaration point onward, so "is this name bound anywhere in the
function?" wrongly refuses a use that PRECEDES the shadow, and wrongly
refuses one whose shadow is in a sibling block. Both are rows.

10 rows, exit 6 on failure. Non-vacuity **run**: a reckless resolver fails
4 and exits 6; a timid one fails 2. A resolver that is merely conservative
fails this gate exactly as a reckless one does.

### THE WALKER HALF

Vendored verbatim from `cmd/compile/internal/ssa/rewrite.go`:

    func log64(n int64) int64 { return int64(bits.Len64(uint64(n))) - 1 }
    func ntz64(x int64) int   { return bits.TrailingZeros64(uint64(x)) }

Two functions, not one, because a dispatch table with a single entry is
indistinguishable from a hard-coded answer. `math/bits` is first because
§G15 **proved** `bitLen` correct, so the rung tests the mechanism against
settled semantics; `len64_model_is_the_proved_spec` closes that by `rfl`.

The discriminating arguments are the negative ones — `uint64(n)` wraps:

| call | `gc` | what a wrong model gives |
| --- | ---: | --- |
| `log64(-1)` | 63 | no wrap: `Len64` of a negative is not a `Nat` |
| `log64(0)` | **-1** | 0 if `Len64(0)` were special-cased to 1 |
| `ntz64(0)` | **64** | 0 — Go DEFINES this as the width |
| `ntz64(MinInt64)` | 63 | the single set bit is the top one |

`ntz64(0) = 64` and `log64(0) = -1` pull in **opposite directions on the
same zero argument**, which is why both functions are here. 32 guards
(counted, per §G20's rule), every value `printf`-ed from `gc`, 6
non-vacuity flips run.

Unmodelled packages refuse as `environment` **naming the callee** —
`math/rand.Intn is not modelled`, not "selector call" — which is §5.2's
bucket retiring by widening, and makes the refusal stream a ranked
worklist (§G8's recommendation 2). Gated, including that it is never
`undefined`: the zero-UB gate holds across a package boundary.

### THE REACH: +0, and the charter's +7 was optimistic

| vocabulary | files |
| --- | ---: |
| baseline (§G20) | 680 |
| **+ E1 as landed** (`Len64`, `TrailingZeros64`) | **680 (+0)** |
| + if ALL of `math/bits` were modelled | 687 (+7) |

**The conjunctive law again, now at the PACKAGE-FUNCTION level.** §G21
priced `math/bits` at +7 from the package ranking, but a file needs every
function it calls, not the package's name. The 7 files are exactly:

`crypto/internal/fips140/edwards25519/scalar_fiat.go`,
`nistec/fiat/p{224,256,384,521}_fiat64.go`, `math/big/arith.go`,
`strconv/itoa.go`

and what blocks them, measured: **`Add64` 2,077 sites, `Mul64` 1,038,
`Sub64` 186** — plus `Div`. All **multi-value returns**.

§G19's retraction applies to this +0 exactly as it did to `RangeStmt`: it
means *not a rung on its own at this vocabulary*, not *worthless*. E1's
deliverable is the mechanism, and the mechanism is real, gated, and
reusable by every package that follows. But the honest label on this
landing is **+0**, and the standing coverage table does not move.

That is the third time this lane's own published estimate has been
corrected by its own census (§G13, §G21, now §G22), and the second time
the correction was to a number *this lane* had written one rung earlier.

### NEXT: multi-value returns, priced by this rung

Not another package. `Flow.returned` carries one `GoVal`, and that single
fact blocks:

* all 7 of `math/bits`' files, and
* **88% of `math/bits` call sites** (`Add64` 54.7%, `Mul64` 27.7%,
  `Sub64` 5.5%),

and it is a WALKER rung, not an extractor one — so the alternation the
recalibration asked for is what the census says to do, not a scheduling
convention. E2 (`go/types`) is unchanged: sized only after E1's refusal
worklist says which types need resolving, and E1 now produces that
worklist.

One thing the rung surfaced and did not model: `bits.UintSize` is a
package-level **constant**, not a function. Package constants are a
distinct resolution kind and are not in this rung's vocabulary.

MM-oracle untouched — Thomas's. `fallthrough` deferred (4.0%).

---

## G23 — MULTI-VALUE RETURNS: Go has no tuple values, and the reach is +0 again (2026-08-24)

The walker rung §G22's census called. The mechanism is built and gated;
**the advance reach claim of +7 did not land, and this entry says so
first.**

### THE CENSUS: how the corpus spells it

| spelling | sites |
| --- | ---: |
| `a, b = f()` / `a, b := f()` — destructuring | **22,315** |
| ...`:=` form | 14,951 |
| ...`=` form | 7,364 |
| ...**with a BLANK `_` discarding a result** | **7,964 (35.7%)** |
| `return e₁, …, eₙ` | 13,991 |
| functions returning ≥ 2 | 6,675 (exactly 2: **85.9%**) |
| ...named results / anonymous | 3,328 / 3,347 — an even split |
| `a, b = 1, 2` — PARALLEL assignment | 3,288 |

Two things the census settled that guesswork would not have:

* **The blank is not an edge case.** More than a third of all
  destructurings discard a result, so `_` had to be a real discard from
  the first commit, not a variable named `"_"`.
* **`a, b = 1, 2` is a DIFFERENT feature** wearing the same `go/ast`
  node. One node shape, two features; the frontend separates them by
  counting the right-hand side, and this rung models only the first.

### THE VALUE MODEL: there is no tuple value, and that is checkable

The obvious shape is a `GoVal.tupleV`. It is wrong, and `gc` says so:

    x := bits.Add64(1, 2, 0)
    // assignment mismatch: 1 variable but bits.Add64 returns 2 values

Multi-valuedness is a property of the **call site**, never of a value. A
tuple value would let the model accept programs Go rejects — the same
error class as modelling an array as a slice header (§G20), and caught
the same way: by asking what the wrong model would permit.

So `Flow.returned` carries a **list** (`[]` bare, `[v]` single, `[a,b]`
multi — one constructor, mirroring Go's single `ReturnStmt`), there is no
tuple `GoVal`, and a multi-valued call reaching a single-value context
REFUSES rather than yielding its first result. That refusal matters:
silently taking the first value is exactly how a carry gets dropped.

### THE FUEL DECISION, and why a settled proof stayed settled

Routing `return e` through the n-ary `evalArgs` costs one extra fuel
level, which would have moved the fuel bound of every single-valued proof
— including §G15's proved `bitLen_correct`. Go's semantics do not
distinguish the two, so `.ret [e]` keeps its **own arm**. The settled
proofs did not move, and `ret_one_run` in `Spec.lean` now carries the
epilogue's shape so future rungs cannot quietly re-break them.

### A DUPLICATE SPECIFICATION, removed

`bits.Len64` needed the same recursion `Examples/go/bitlen` had defined
locally, and Lean's ambiguity error found it. Two copies of a
specification is precisely what "the model always matches the code"
exists to prevent — they can drift and nothing says so. `bitLenSpec` now
lives once, in `LeanModels/Go/Packages.lean`, so `Len64`'s model IS
definitionally the function §G15 proved `bigmod.bitLen` computes.

### THE ACCEPTANCE, and a model that passes 5 of 8 rows

`crypto/internal/fips140/aes/ctr.go`'s `add128`, vendored verbatim — four
lines holding the whole rung: `:=` destructuring, `=` destructuring **with
a blank**, a multi-valued return, and Go's **redeclaration** rule (`lo` is
a parameter, so `lo, c := …` assigns `lo` and declares only `c`).

The carry from the first `Add64` feeds the second, so a single-return
model makes it zero forever:

| `⟨lo, hi, x⟩` | `gc` | carry-dropping model |
| --- | --- | --- |
| `⟨0,0,0⟩`, `⟨0,0,1⟩`, `⟨1,2,3⟩`, `⟨MAX-1,7,1⟩`, `⟨MAX,0,0⟩` | — | **agrees on all five** |
| `⟨MAX, 0, 1⟩` | `⟨0, 1⟩` | `⟨0, 0⟩` |
| `⟨MAX, 5, 1⟩` | `⟨0, 6⟩` | `⟨0, 5⟩` |
| `⟨MAX, MAX, 1⟩` | `⟨0, 0⟩` | `⟨0, MAX⟩` |

**Five of eight rows agree.** A single-return model is not obviously
broken; it is quietly wrong exactly where carries propagate. Only the
three ripple rows separate them, and all three flips were run.

17 guards (counted), every value `printf`-ed from `gc`.

### THE NON-VACUITY FLIP CAUGHT A GUARD THAT CHECKED NOTHING

The blank-discard row was written with a `| _ => true` fallback and a
world whose parameters were unbound — so the body REFUSED, the fallback
fired, and the row passed without testing anything. Flipping it produced
**0 errors**, which is how it was found.

The lesson is sharper than "write better guards": **a fallback arm that
returns `true` converts a failing run into a passing row.** Fixed by
binding the parameters and making the fallback `false`, plus a companion
row asserting the run actually SUCCEEDS, so the assertion cannot pass by
failing. That is the third distinct vacuity shape this lane has hit
(§G13's hand-typed oracle, §G15's byte-identical non-vacuity section, now
the swallowing fallback).

### THE REACH: +0, and the +7 needs one more rung

The advance claim was the 7 files §G22 identified. It did not land:

| vocabulary | files |
| --- | ---: |
| baseline (§G20, §G22) | 680 |
| **+ multi-value returns and `Add64`** | **680 (+0)** |
| + if ALL of `math/bits` were modelled | 687 (+7) |

`Add64` was 2,077 of the blocking sites and is now modelled, but the
files need **every** function they call. What still blocks all 7:

`Mul64` (1,038 sites), `Sub64` (186), `Add` (7), `Sub` (5), `Mul` (4),
`Div` (1), `LeadingZeros` (1), `TrailingZeros` (1) — and **`UintSize`,
which is not a function at all**: `const UintSize = uintSize`. Package
CONSTANTS are a resolution kind the extractor does not have, so the +7
needs both the remaining functions and a new (small) extractor capability.

This is the conjunctive law a fourth time, and the second rung running to
report +0. The distinction worth keeping: §G22 was +0 because a *mechanism*
unlocks nothing by itself; §G23 is +0 because the mechanism's first
*consumer* was only one of nine. Both are real, neither is failure, and
the standing coverage table does not move for either.

**Next, and it is now a small, purely additive rung**: the remaining
eight `math/bits` functions plus package constants — every one of them
unblocked by this rung, none needing new walker machinery, and together
they are the +7. That is the first time this lane can name a rung whose
reach is fully priced in advance and whose blockers are all removed.

MM-oracle untouched — Thomas's. `fallthrough` deferred (4.0%).

### VERDICT

`tools/triad.sh --lane go --classify --gates '…docs_check; diff_test;
script_corpus; census.sh --resolve'` — **green**.

* **Tree certified**: `b2d63096a900` — verified equal to this landing's
  working tree, not inferred from the ticket's title.
* **Elaboration witness**: **30 Built, 2 Replayed**, and every one of the
  eleven Go-tier modules — `LeanModels.Go`, `.Stmt`, `.Spec` and all
  eight `Examples.go.*.guards` — is **Built**. The build was a real
  elaboration, not a cache replay. (The 330 `Replayed` lines in the triad
  log belong to the gate phase's runner, not the build phase; duration
  corroborates but Built/Replayed is the witness.)
* Queued **4,511 s**; build phase **11 s**; `TRIAD DONE` at 01:41:31.
* `docs_check` 91/91, `diff_test` 0 failed, `script_corpus` 65/0,
  resolver self-test 10/0.

---

## G24 — THE `math/bits` COMPLETION RUNG: +7 predicted, +7 measured (2026-08-24)

§G23 priced this rung **in advance** at +7 files and named every blocker.
It landed exactly:

| | predicted (§G23) | measured |
| --- | ---: | ---: |
| all of `$GOROOT/src` | 680 → **687** | 680 → **687** |
| the library only | 587 → **594** | 587 → **594** |

The blocker list is now empty for all seven files. This is the second
exact reach prediction this lane has made (§G20's `[N]T` at +76 was the
first), and unlike that one it was called a **whole rung** ahead, with
its prerequisites named and discharged separately.

### THE CONSTANT IS A DIFFERENT KIND

`const UintSize = uintSize` is not a function, and Go enforces the
difference — `bits.UintSize()` does not compile. So it gets its own node
(`Expr.pkgConst`) and its own extractor rule: a selector **not in call
position**. Modelling it as a nullary `callPkg` would let the model accept
a program `gc` rejects, which is the same test that ruled out tuple values
in §G23 — *ask what the wrong model would permit*.

The resolver's battery grew to **13 rows**, and the two new ones are
gated both ways: a resolver that cannot tell a constant from a call fails
them (verified — 2 failures, exit 6), and a shadowed constant is still
not resolved.

### `Div` PANICS, so the result type had to widen

`bits.Div` panics on a zero divisor and on a quotient that will not fit —
`"runtime error: integer divide by zero"` and `"runtime error: integer
overflow"`, both printed from `gc`. A plain `Option` cannot say that, so
`pkgCall` now returns `PkgOutcome` with **three** cases:

| case | meaning |
| --- | --- |
| `values` | it computed something |
| `panics` | **Go DEFINES this**; the program's outcome |
| `notModelled` | this tier's limit → `environment` refusal naming `pkg.fn` |

Folding `panics` into `notModelled` would report a program's own defined
behaviour as a gap in the model — the §5.2 mis-bucketing §G14 paid for
once already. `div_by_zero_panics_not_unmodelled` states the distinction
as a theorem so it cannot be quietly re-collapsed.

### THE SURFACE LIST WAS WRONG THE MOMENT IT WAS WRITTEN

`modelledPkgFuncs` named `("math/bits", "Len")` while `pkgCall`
implemented only `Len64`. Nothing caught it, because the list was prose
in the shape of data — a declaration of support that no test read.

It now carries each function's **arity** and is checked:

    theorem surface_is_honest :
      modelledPkgFuncs.all (fun t => (pkgCall t.1 t.2.1 …).isModelled) = true := by rfl

`rfl`, not `native_decide` — the axiom ledger stays `[propext,
Quot.sound]`, with no `ofReduceBool`. `Len` is now implemented too.

The general lesson, and it is not specific to Go: **a list that says what
a model supports is a claim, and an unchecked claim drifts on the first
edit.** This one drifted within a single rung.

### THE ACCEPTANCE: a carry folded into the high word

`math/big/arith.go`'s `mulAddWWW_g`, vendored verbatim — from one of the
seven files this rung unblocks:

    func mulAddWWW_g(x, y, c Word) (z1, z0 Word) {
        hi, lo := bits.Mul(uint(x), uint(y))
        var cc uint
        lo, cc = bits.Add(lo, uint(c), 0)
        return Word(hi + cc), Word(lo)
    }

The discriminator is `hi + cc`: `Add`'s carry is added INTO the high
word, so a model that dropped it returns the same low word and a high
word one too small. At `⟨MAX, MAX, MAX⟩` `gc` gives `⟨MAX, 0⟩`; the
carry-dropping model gives `⟨MAX-1, 0⟩`.

`Word` is `uintptr` (64-bit here) and the frontend emits its conversions
as `uint64` — sound for arithmetic, losing only type identity, which
costs nothing at a rung with no methods.

**50 guards** (counted), every value `printf`-ed from `gc`, **7
non-vacuity flips run** — including both `Div` panic messages and
`LeadingZeros(0) = 64` against the tempting `0`.

### NEXT

The reach ladder is back to the extractor. With `math/bits` complete, the
next packages by the §G21 ranking are `syscall` (3,245 selections — but
`environment` by nature, so it retires as a refusal that NAMES rather
than as reach), then `fmt` (2,396), `reflect`, `io`, `errors`. `fmt` is
the first that needs formatting semantics and variadics, so it should be
priced against the walker's own frontier before it is assumed next.

The honest note on E2 (`go/types`) is unchanged: it is sized only after
E1's refusal worklist says which types need resolving, and that worklist
now exists.

MM-oracle untouched — Thomas's. `fallthrough` deferred (4.0%).

### VERDICT

`tools/triad.sh --lane go --classify --gates '…docs_check; diff_test;
script_corpus; census.sh --resolve'` — **green**.

* **Tree certified**: `2c4217cdabc7`, verified equal to this landing's
  working tree.
* **Elaboration witness**: **29 Built, 2 Replayed**. `LeanModels.Go.Stmt`,
  `LeanModels.Go`, `Examples.go.bitspkg.guards` and
  `Examples.go.pkgcall.guards` are **Built**. `LeanModels.Go.Packages` was
  NAMED in the build target list and emitted no line — lake found it
  current from the authoring build of this same tree — and its dependents
  were Built against it. Saying "all Go modules Built" would be wrong;
  this is what the log actually witnesses.
* Queued **2,131 s**; build phase **12 s**.
* `docs_check` 91/91; `diff_test` **1,475 cases, 0 failed**;
  `script_corpus` 65/0; resolver self-test **13/13**.

---

## 2026-08-24-c-16 — INBOUND FROM THE C LANE: Go lane's to renumber or close

*Id kept in the C namespace; nothing minted in the Go sequence. Filed after
reading `LeanModels/Go/Obs.lean` in full — its §1b analysis of the match
DISCRIMINANT problem is what told this lane which shape to lift, and it is
credited in `LeanModels/Core/Outcome.lean` §4 rather than absorbed.*

### YOUR RUN SEAM IS NOW IN `Core`, GENERIC. `Obs.lean` §1-§3 can become instances.

`LeanModels/Core/Outcome.lean` §4 (landed `2026-08-24-c-15`) carries
`SemMWith.run_bind` and its family, generic in all four of `SemMWith`'s
parameters. **`GoM := SemMWith GoWorld Panic SpecRef Unit`**, so every row in
`Obs.lean` §1-§3 is now a one-liner:

```
@[go_run] theorem run_bind (x : GoM α) (f : α → GoM β) (w : GoWorld) :
    (x >>= f) w = (match x w with …) := SemMWith.run_bind x f w
```

…and the same for `run_bind_ok`, `run_bind_loud`, `run_bind_panic`
(Core spells it `run_bind_raise` — the `ρ` channel, language-neutrally),
`run_pure`, `run_get`, `run_set`, `run_modify`, `run_raiseIn`,
`run_exhausted`, `run_map`, `run_seqRight`. **`run_refuseGo` stays yours**:
`r.toCore π` is a Go-side translation, not a stack fact.

**Why this is being told to you rather than done for you.** §9.2 is
consolidation BY TOUCH, and this lane is not in your file. The C tier adopted
in the same commit that landed Core's copy because it was the lane that was
there; Go adopts whenever it next has `Obs.lean` open, and **nothing here
asks for a commit today.** Until then the tree holds two proofs of one fact,
which Core §4 states in the open — recorded rather than silent is the whole
point of §9.3.

**One correction offered to a sentence, not a defect.** `Obs.lean`'s header
says *"The ORDER lifts; the CONGRUENCES don't"*, and it is right about
Python's `Res`, which carries an `.exn` arm this stack does not and whose
`bind` is a different function. It is not right about a second tier that
INSTANTIATES this stack, and the C tier was that second tier. The test turned
out to be mechanical:

> **A congruence generic in the SUBSTRATE'S OWN parameters is not a per-tier
> congruence. Whether you are looking at one or the other is decided by
> whether the PROOF mentions a tier type — and neither of ours did.**

Your `bind` proof and this lane's differed by exactly four type
substitutions (`GoWorld`/`Mem`, `Panic`/`Refusal`, `SpecRef`/`CDetail`,
`Unit`/`Mem`) and nothing else.

*Renumber into your sequence or close it — the call is yours.*

---

## G25 — VARIADICS: packing allocates, spreading does not; +52 predicted, +52 measured (2026-08-24)

### THE CENSUS THAT CHOSE THIS RUNG OVER `fmt`

`fmt` was the presumed next step. The census says it is a rider, not a
rung. Split by what each `fmt` selection needs (library-only, 2,396 —
reconciling exactly with §G21's figure):

| needs | selections | share |
| --- | ---: | ---: |
| variadics **and** verb parsing | 2,105 | **87.9%** |
| variadics only | 274 | 11.4% |
| neither | 17 | 0.7% |

Over all of `$GOROOT/src` (6,403) the split is the same to a tenth.

Priced as REACH, the two halves are not close:

| vocabulary | all of `src` | library |
| --- | ---: | ---: |
| baseline (§G24) | 687 | 594 |
| **+ variadics alone** | **739 (+52)** | **644 (+50)** |
| + variadics + `fmt` minus the `Fprint` family | 742 (+3) | 646 (+2) |
| + variadics + ALL of `fmt` | 742 (+3) | 646 (+2) |

**Variadics are worth seventeen times what `fmt` adds on top**, and the
`Fprint` family costs nothing extra — so `io.Writer` was never the
binding constraint, though 2,493 of `fmt`'s 6,403 selections (38.9%) are
`Fprintf`/`Fprintln`/`Fprint` and it would have been natural to assume
interfaces gated them.

Two structural findings:

* **`fmt` without variadics is not a rung at all** — every one of its
  entry points is variadic. The ordering was never a choice.
* `fmt` contributes **+3 against 6,403 call sites**. Call-site frequency
  is not reach (§G21's lesson, third reproduction).

Variadics also stand on their own: **520** variadic parameter
declarations, **1,757** spread call sites, **224** distinct variadic
function names — a consumer base far wider than `fmt`.

### THE VALUE MODEL: the marker cannot live at the call site

`f(1,2,3)` packs its surplus arguments into a slice **only if `f` was
declared `f(xs ...T)`**; the same call text against a fixed-arity `f` is
an arity error. So the callee's signature decides, and `FuncTable` gained
a variadic marker — `List (String × List String × Bool × List Stmt)`.
`arityOk` states the fixed and variadic rules in one place so the three
call paths cannot drift.

### THE ACCEPTANCE: one callee, two call forms, opposite aliasing

Measured against `gc` with a callee that writes `xs[0] = 'Z'`:

| call | the CALLER's slice afterwards |
| --- | --- |
| `clobber(s...)` | **`"Zbc"`** — the callee ALIASED it |
| `clobber(a, b, c)` | **`"abc"`** — packing gave it a FRESH array |

The function is identical; only the call form differs. **A model with one
code path for both fails one row whichever way it chooses** — it cannot
pass both. That is why `callDots` is its own node rather than a flag: the
two forms differ observably, and §G14's rule is that a distinction the
frontend can make must not be re-made inline.

`clobber()` returns **0** — a variadic parameter with no arguments is a
slice of length zero, and it always exists.

13 guards, every value `printf`-ed from `gc`, **5 non-vacuity flips run**
including both halves of the aliasing pair.

### THE PREDICTION

Called in §G25's census **before building**: `687 → 739` and
`594 → 644`. Measured after: **`687 → 739` and `594 → 644`.**

Third consecutive exact reach prediction (§G20 `[N]T` +76, §G24
`math/bits` +7, now +52). The instrument that makes them is
`construct_census.go --reach` plus the package-aware probe; the practice
that makes them honest is pricing the rung before writing the code, so
the number cannot be fitted afterwards.

### A SETTLED PROOF MOVED, AND WAS PUT BACK

`bitLen_correct` broke: its arity hypothesis named the inline length
comparison that `arityOk` replaced. It is one line — `harity` in place of
`hlen`, plus `bindBySig` in the simp set — and the theorem is unchanged.
Worth recording because it is the second time a walker-wide refactor
touched §G15's proof (§G23's n-ary `.ret` was the first), and both times
the fix was a hypothesis restatement rather than a re-proof. That is the
payoff of the spec-half/interpreter-half split: the mathematics did not
move, only the interpreter row that names the check.

### NEXT

`fmt` is now unblocked but priced at **+3 / +2**, which does not justify
verb-parsing semantics yet. The next rung should be re-censused from the
current frontier rather than assumed — with variadics landed, the
frontier table is stale and `Ellipsis` has left it.

MM-oracle untouched — Thomas's. `fallthrough` deferred (4.0%).

### VERDICT

`tools/triad.sh --lane go --classify --gates '…'` — **green**.

* **Tree certified**: `dae3ca43c408558869c1e6e61ce79a330d2dbfa3`, verified
  equal to this landing's working tree, and recorded in the greens ledger
  against ticket `1787573505393285000-44296-go` with
  `Examples.go.variadic.guards` among its targets.
* **Elaboration witness**: **36 Built, 2 Replayed** — all twelve Go-tier
  modules **Built**, `Examples.go.variadic.guards` and
  `LeanModels.Go.Stmt` among them.
* Queued 139 s; build phase 16 s.
* `docs_check` 91/91; `diff_test` **1,500 cases, 0 failed**;
  `script_corpus` 65/0; resolver self-test **13/13**.

---

## G26 — THE RE-CENSUS AFTER VARIADICS: the frontier is spent, and `syscall` is a mirage (2026-08-24)

Census only. `Ellipsis` left the frontier when §G25 landed, so the table
was stale; this is the re-run, and it changes what "next" means.

### THE CONSTRUCT FRONTIER IS EFFECTIVELY OVER

| construct | alone |
| --- | ---: |
| `SelectorExpr/pkg` | +533 |
| `SelectorExpr/value` | +117 |
| `MapType` | +15 |
| `InterfaceType` | +8 |
| `SwitchStmt`, `FuncLit` | +2 each |
| the other nine | **+0** |

Nine of fifteen remaining constructs are worth **nothing**, and the
largest thing that is not a selector is `MapType` at +15. The walker's own
vocabulary has essentially stopped paying — §G20 first said so and it is
now sharper.

### SO THE QUESTION IS WHICH PACKAGE, AND SELECTION COUNT ANSWERS IT WRONG

Ranked by **executable** reach — files that become fully steppable if
that package were modelled — against selection count:

| package | selections | +files (all `src`) | +files (library) |
| --- | ---: | ---: | ---: |
| `syscall` | 3,307 | **+61** | **+58** |
| **`strconv`** | 673 | **+26** | **+13** |
| `errors` | 2,016 | +11 | +11 |
| `math` | 710 | +7 | +7 |
| `strings` | 2,984 | +5 | +4 |
| **`fmt`** | **6,403** | **+4** | **+3** |
| `io` | 2,214 | +4 | +4 |
| ALL remaining at once | — | +306 | +210 |

`fmt` has **9.5× `strconv`'s selections and a sixth of its reach.**
`strings` has 4.4× and a fifth. This is the fourth reproduction of
"call-site frequency is not reach", and it is now the most reliable way
this lane has of picking wrong.

### `syscall` LEADS AND MUST BE SKIPPED

`syscall` tops the table at +61/+58, and it is not a rung. It **is** the
operating-system boundary: `syscall.Write`, `syscall.Open`. This tier
cannot execute it at any price, so its 3,307 selections retire as
`environment` refusals that NAME the callee — §5.2's bucket retiring by a
better refusal rather than by reach, exactly as §G8 said of the cheap
tier and §G21 said of `unsafe` and `C`.

Counting it as available reach would be the same motivated error §G21
caught in `unsafe`/`C`, one tier up: a package the model will never run
is not a package the model can be credited for. The honest headline is
therefore **`strconv` at +26/+13**, not `syscall` at +61/+58.

### NEXT RUNG, PRICED IN ADVANCE

**`strconv`** — the top MODELLABLE package on both denominators, and the
one whose semantics this lane has already built twice: `runtime.itoa`
(§G18) and `runtime.printuint` (§G20) are the same digit loops, and
§G24's `math/bits` supplies the integer primitives.

Called before building, per the practice that has now been exact three
times running:

> **§G27 `strconv`: 739 → 765 (+26) over all of `$GOROOT/src`;
> 644 → 657 (+13) over the library.**

The rung should be sized by which `strconv` entry points the 26 files
actually call — census first, as `math/bits` was, where 82% of the
package sat behind one missing construct.

MM-oracle untouched — Thomas's. `fallthrough` deferred (4.0%) and now
visibly minor against a +0 frontier.

---

## G27 — THE `strconv` CENSUS KILLED ITS OWN PREDICTION, AND FOUND THE METRIC OVERSTATED (2026-08-24)

Census only. **§G26 predicted `strconv` at +26/+13. The correct figure is
+0**, and finding out cost no code, because the entry-point census ran
first.

### WHAT THE 26 FILES ACTUALLY CALL

Two entry points. Not thirty:

| entry point | uses in those files |
| --- | ---: |
| `FormatInt` | 28 (96.6%) |
| `Itoa` | 1 |

Corpus-wide `strconv` has **30 distinct functions and 673 uses**
(`Itoa` 108, `FormatInt` 86, `Atoi` 76, `ParseInt` 75, `Quote` 48…). The
reach comes from two of them — the vocabulary law paying off again.

And **25 of the 26 files are `*_string.go`**: generated `stringer`
output, all one shape:

    func (i Kind) String() string {
        if i < 0 || i >= Kind(len(_Kind_index)-1) {
            return "Kind(" + strconv.FormatInt(int64(i), 10) + ")"
        }
        return _Kind_name[_Kind_index[i]:_Kind_index[i+1]]
    }

### THAT SHAPE NEEDS TWO THINGS THE WALKER DOES NOT HAVE

* a **method** — `func (i Kind) String()`. `FuncTable` maps a plain name
  to a body and has nowhere to put a receiver.
* **string concatenation** — `"Kind(" + … + ")"`. `binNum` is
  integer-only.

Measured over all 26: **26 need BOTH, 0 are unlocked by `strconv`
alone.** The prediction was not merely optimistic, it was the wrong
construct entirely.

### THE STANDING METRIC WAS OVERSTATED, AND BY HOW MUCH

If the reach probe counted those 26, it was counting others like them.
Audited:

| | counted | declare a method | string concat | either | **honest** |
| --- | ---: | ---: | ---: | ---: | ---: |
| all of `$GOROOT/src` | 739 | 16 | 7 | 22 | **717** |
| library only | 644 | 9 | 7 | 15 | **629** |

**§9.0 is corrected to 717 / 3,803 (18.9%) and 629 / 2,743 (22.9%).**

The cause is precisely the one the coverage table's own guard names — *it
measures SYNTACTIC coverage, an upper bound* — and I wrote that guard and
then used the number as if it were executable anyway. `FuncDecl` is one
`go/ast` kind for two things the walker prices differently, and so is
`BinaryExpr`. That is the **third** instance of the shape after
`ArrayType` (§G20) and `SelectorExpr` (§G21); it should have been looked
for, not stumbled on.

**The deltas survive.** +76, +7 and +52 were each measured with the same
gap-affected files on both sides, so they are unaffected; only the
absolute level was inflated. A wrong baseline and a right delta is the
honest description.

### THE FIX LIVES IN THE GATE

`construct_census.go` now splits both nodes — `FuncDecl/plain` vs
`FuncDecl/method`, and `BinaryExpr` vs `BinaryExpr/strcat` — so the
instrument cannot make this mistake again. It independently reproduces
the audit: `FuncDecl/method` +15 and `BinaryExpr/strcat` +5 against the
audit's 16 and 7 (the instrument's baseline excludes package selectors,
hence the small difference).

### THE REAL NEXT RUNG IS A BUNDLE

Not `strconv`. **Methods + string concatenation + `strconv`'s two entry
points**, which is the conjunctive law for the fifth time — and this time
the parts are worth **+0 each**, the starkest instance yet.

Priced in advance from the CORRECTED baseline:

> **§G28: 717 → 765 (+48) over all of `$GOROOT/src`;
> 629 → 657 (+28) over the library.**

Note the destination is the same 765/657 §G26 predicted; what was wrong
was the baseline and the attribution, not the target. The next report
should say which of those two was actually being tested.

MM-oracle untouched — Thomas's. `fallthrough` deferred (4.0%).

---

## G28 — THE BUNDLE: four parts, each worth +0, together +48 (2026-08-25)

§G27 priced this against the **corrected** baseline, and said so — the
test was whether 717/629 was right, not whether a fourth clean prediction
could be collected. It was right:

| | predicted (§G27) | measured |
| --- | ---: | ---: |
| all of `$GOROOT/src` | 717 → **765 (+48)** | 717 → **765 (+48)** |
| library only | 629 → **657 (+28)** | 629 → **657 (+28)** |

Because the destination was computed independently of the baseline,
hitting it corroborates the correction rather than the streak.

### A FOURTH MEMBER THE CENSUS MISSED

§G27 named three parts. Building found a fourth: **slicing a string**.
The generated shape ends `_Kind_name[_Kind_index[i]:_Kind_index[i+1]]`,
and `SliceExpr` is one `go/ast` node covering two operations this walker
prices differently — slicing a slice yields a header, slicing a string
yields a **string**.

That is the shape for the **fourth** time (`ArrayType` §G20,
`SelectorExpr` §G21, `FuncDecl` §G27, now `SliceExpr`), and it carries a
limit worth recording: **the first three splits are syntactic and this
one is not.** `Len == nil`, an import table and `Recv != nil` are all
decidable from the AST; string-versus-slice needs TYPES. So the census
instrument can gate the first three and cannot gate this one — the
residual over-count it leaves is bounded only by `go/types`, which is
rung E2. The metric's ceiling is now a known quantity rather than an
open worry.

It did not need gating in the end, because both operations are modelled.

### THE PARTS ARE WORTH +0 EACH

| part | alone |
| --- | ---: |
| methods | +0 |
| string concatenation | +0 |
| string slicing | +0 |
| `strconv`'s two entry points | +0 |
| **all four** | **+48** |

The conjunctive law's starkest instance yet — four parts, every one
worthless alone. §G19's retraction of the `+0` law is what makes this
legible: a `+0` is a statement about the current vocabulary, never a
ranking.

### THE METHOD IS THE EXTRACTOR'S PROBLEM

`FuncTable` maps a plain name to a body and has nowhere for a receiver.
Rather than widen it, the extractor mangles a method to `Type.Method`
with the receiver as first parameter — §G22's division of labour, gated
by four new rows in `census.sh --resolve` (**17/17**): pointer and value
receivers key the SAME (Go forbids both, so it cannot collide), generics
key on the bare type, and a plain function is not a method.

This models the DECLARATION. Calling one needs `x.M()` dispatch — a value
selector, still rung E3 — and the 26 files only declare.

### THE ACCEPTANCE

`go/constant/kind_string.go`'s shape, end to end. 19 guards, every value
`printf`-ed from `gc`, **6 non-vacuity flips run**. The rows that
separate models:

| row | what a wrong model gives |
| --- | --- |
| `Kind(0)` = `"bool"` | cannot slice a string at all |
| `Kind(3)` = `"Kind(3)"` | takes the in-range branch |
| `Kind(-1)` = `"Kind(-1)"` | `"Kind(1)"` — the sign dropped |
| `FormatInt(MinInt64)` | overflows negating it, as Go's own `int64` would |
| `"\xff\xfe" + "!"` = `[255,254,33]` | re-encodes to five bytes |

The last is §G15 paying off a second time: a Go string is a `List UInt8`,
so concatenation is `++` and high bytes survive. A `String`-based model
would have failed that row without anyone noticing the reason.

### THE SURFACE LIST GOT STRICTER, BECAUSE IT HAD TO

`FormatInt` is **conditionally** modelled — base 10, refusing every other
base. `surface_is_honest` tested each entry with the argument `1`, which
would have failed it, so the list would have had to omit `FormatInt`
(under-claiming) or assert it at a base it refuses (failing).

Entries now carry **sample arguments** instead of an arity. Both lies are
caught, run: claiming an unimplemented `strconv.Atoi` fails, and claiming
`FormatInt` at base 16 fails.

### NEXT

Re-census. The bundle closed four gaps at once and `strconv` is now
modelled at two entry points; the frontier that priced §G27 is stale.

MM-oracle untouched — Thomas's. `fallthrough` deferred (4.0%).

### VERDICT

`tools/triad.sh --lane go --classify --build-target …×12 --gates '…'` —
**green**. `LOCK ACQUIRED after 10104s as 'go 53190'` → `BUILD GREEN`
12:46:41 → `TRIAD DONE (build exit 0, gates green)` 12:47:57.

* **Tree certified**: `e23a64afecf48c07dc1a989a654c61dc3a5172c0`, equal to
  this landing's working tree.
* **Coverage**: the union line records all twelve targets entering the
  build set — the eleven guard modules plus `LeanModels.Go`. This is what
  the re-ticket existed for: the FIRST tenure auto-scoped to four modules
  while `Stmt.lean`'s change is imported by eleven, and a green whose
  scope excludes the importers is not evidence about them.
* **Elaboration witness**: **0 Built, 15 Replayed.** Every target was
  replayed, because this lane had already built all eleven locally at the
  identical tree while checking the post-rebase state, warming the cache
  before the ticket was enqueued. So the elaboration DID happen at this
  tree — under authoring, not under tenure — and this run witnesses
  artifact currency, not fresh elaboration.

  Recorded rather than rounded up: `Built`/`Replayed` is the elaboration
  witness, and a lane that pre-builds its own targets destroys that
  witness for its own ticket. **The practical rule this yields: verify
  post-rebase with a SCOPED build of what you changed, not the whole
  target set, or purge before enqueueing.** §G24 hit a one-module version
  of this; at twelve targets it is total.
* `docs_check` 91/91; `diff_test` **1,508 cases, 0 failed**;
  `script_corpus` 65/0; resolver self-test **17/17**.

---

## G29 — THE FLEET FIELD-COLLISION SWEEP: absent here, and the check found a different one (2026-08-25)

The sweep asked whether any field this lane's extractor writes could be
overwritten by `go/ast`'s own property set when source is copied in — ES's
defect, where a source's own `kind` property silently won over the node
type written into `kind`.

### THE ANSWER IS NO, AND HERE IS WHAT PROVED IT

The extractor writes into two namespaces that both mix instrument-written
keys with source-derived ones, so both were tested rather than argued:

| namespace | check | result |
| --- | --- | ---: |
| kind tags (`fileKinds`) — bare `go/ast` type names **and** synthetic sub-kinds | do any of the 52 `go/ast` node type names contain `/`? | **0** |
| `FuncTable` keys — plain function names **and** mangled `Type.Method` | do any of 46,271 function declarations have `.` in the name? | **0** |

Disjoint **by construction** in both: `go/ast` type names and Go function
names are identifiers, and neither `/` nor `.` is an identifier
character. A source-derived value cannot land on an instrument-written
key, in either direction.

Negative results, with the runs that established them.

### BUT THE SAME PROBE FOUND A REAL COLLISION OF AN ADJACENT SHAPE

Asking *"can two declarations mangle to the same key?"* — not the sweep's
question, but one step along the same axis:

    distinct mangled keys 14,513 ; claimed by MORE THAN ONE package 1,037

`Scope.String` in three packages, `Label.String` in two,
`response.writeCGIHeader`, `dumper.printf`. Not reachable while the
extractor ingests one package at a time — every acceptance case is
single-package — and **guaranteed** the moment E2 or E3 ingests more,
which is precisely what they are for.

So the sweep's shape was absent and the sweep still paid, because the
check that proves a namespace safe is the same check that finds it
unsafe one axis over. That is the argument for running these against
lanes that expect to pass.

### THE FIX IS THE SWEEP'S OWN LESSON

A namespace that must stay disjoint is made disjoint **by construction**,
not left disjoint by luck. Keys are now qualified by the package's import
path — unique per package by Go's module rules — so they cannot collide:

    go/types.Scope.String   vs   cmd/compile/internal/types2.Scope.String

Measured after: **15,809 qualified keys, 0 claimed by more than one
package.** Gated by two new rows in `census.sh --resolve` (**19/19**),
one asserting the qualification and one asserting that the same
`Type.Method` in a different package yields a different key.

MM-oracle untouched — Thomas's. `fallthrough` deferred (4.0%).
