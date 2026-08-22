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
