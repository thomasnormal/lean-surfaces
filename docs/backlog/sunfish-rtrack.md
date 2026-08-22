# Backlog — sunfish R-track (`RecursionStep` campaign)

Per-lane backlog under docs/family-architecture.md §9.5. Ids are
`YYYY-MM-DD-sunfish-rtrack-<n>`; no reservation is needed because the lane name
makes them unique, which is the point of the scheme. Sections up to §L80 for this
lane live in the shared `docs/backlog.md` archive and every `§Lnn` reference in
the Lean sources keeps resolving there.

**Lane scope:** R1–R3e (the `RecursionStep` campaign at depth 1) plus the R2
ordering line. The depth-0 ground is the calmness/census lane's (§L32), and the
two do not overlap.

## 2026-08-22-sunfish-rtrack-1 — THE `pst` LOCALITY LEMMA and the SEARCHED ROUND, rebuilt after a purge

Two landings, one triad — and the section is also the record of losing them once.

### 1. `PstAt` — what the world enters `Position.value` through

The observation takes one reading of the four `value_runs_*` signatures: **the
world appears in exactly TWO hypotheses** — `pst` in the globals and the shipped
table at its slot. Everything else is board, indices, move. So the world's entire
contribution to `Position.value` is one predicate, and naming it converts *"does
the value survive this step?"* into *"does `PstAt` survive this step?"* — a
question about the HEAP rather than about the interpreter. That is F1's
*frame-lookups-need-altitude* law arriving at the generator layer.

| declaration | |
|---|---|
| `PstAt` | the two facts, named |
| `PstAt.push` / `.append` / `.update_ne` | stable under the three shapes a generator step leaves: a push, a run of pushes, and a write at a slot that is not `pst`'s |
| `valueRuns_quiet_of_pstAt` | the quiet arm with the world entering ONLY through the predicate |

General heap facts reused rather than re-proved (`Heap.get?_push_of_get?`,
`Heap.get?_update_ne`). It lives in `value_bound.lean` because that is what the
predicate is about — and because `mvOf` is private there, which is itself the
argument for the placement.

**The §L80 residue is now ONE line in the consumer's own vocabulary:** *the inner
generator's steps preserve `PstAt`.* §L58 measured that they only grow the heap;
it is not derivable from `IterSteps`, which says nothing about slots a step did
not touch. Before `PstAt` that obligation could not be stated without unfolding
four theorem signatures.

### 2. §14 — branch 5 composed, and `break_skips`

§L47 said branch 5's five statements were "all gated" and stopped. **Gated is not
composed**, and the difference is where the round's world lives: `cap_line_low`,
`break_skips` and `move_depth_low` run at `w`; `search_line` moves it to `w₂` in
two hops; `live_updates` runs at `w₂` and reads `MATE_UPPER` off ITS globals.

`break_skips` was the missing gate — `break_fires`' twin at a cap that CLEARS the
window, one `if_neg`, and exactly what separates R3a's arm from R3b's.

**The frame is a four-`Env.set` tower and it does not collapse.** `cap`,
`move_depth`, `score`, `live` are four different keys, so `Env.set_set` never
fires and every later gate's lookups are `Env.lookup_set_ne` through the ones
before it — mechanical, not free, and why the composition is a theorem.

### A CROSS-LANE DUPLICATION, found by reading before writing

`qs_stream.lean`'s `branchFalseSilent` is **literally** `fold_depth1.lean`'s
`branch_false_silent` — same statement, same proof shape, two lanes, two names.
Neither mentions sunfish. By §L55's rule they belong in `LeanModels` beside the
lemmas they compose, and one should be deleted.

First time lift-don't-copy has caught a duplication BETWEEN lanes rather than
within one, and the mechanism deserves naming: neither lane could see the other's
file (`fold_depth1` and `qs_stream` are siblings, not ancestors), so **the import
graph made the duplication invisible to both.** The general layer is the only
place two lanes can both look — the argument for lifting, stated as a
coordination fact rather than a taste.

### THE PURGE, and what recovery actually rested on

Both landings were proved, committed locally, and **lost unpushed** when
`/private/tmp` was purged for the third time. The commit that survived was the
one that had been pushed (§L80). What made the rebuild exact was not the backlog
this time but the fact that both proofs were still in the working transcript —
which is luck, not method. **The method is: push per landing, and when the triad
queue makes that slow, the queue is the thing to fix, not the push.** This
session's two landings sat unpushed for hours purely because a triad could not
get a lock.

### Two operational findings, both paid for

**`pkill -f <path>` does not kill a build.** `lake`'s own command line is just
`lake build` — no path — so a pattern matching the clone directory matches the
`lean` workers and misses their parent. The parent then respawns workers and the
build survives as an orphan with `ppid 1`, running unlocked. That is what
happened here, and the orphan was most of a load-38 spike; killing it dropped the
box to 11. **Kill a build by its `lake` process's CWD, not by a command-line
pattern.**

**`cp -Rpc` of a warm `.lake` from an idle peer: 7.8 GB apparent, ~1 GiB actual,
33 s.** APFS block sharing, measured here after the disk sweep deleted this
lane's `.lake`. The `-p` matters — §L52 recorded that `cp -Rc` without it loses
mtimes and Lake re-elaborates from cold.

### Triad

Run through `tools/triad.sh --lane sunfish_merged` (first adoption in this lane):
`lake build` **exit 0**; `docs_check` 83/83, 24 illustrative-exempt; `diff_test`
**1394 cases, 0 failed**, 118 whitelisted, 1276 matched; `script_corpus` 65
scripts, 0 failed, 50 matched, 15 loud. No `sorry`, no `native_decide`.

### A MEASURED DEFECT IN AMENDMENT 11's RSS LINE

The first build attempt was killed by the 3 GB own-chain RSS line, and the
measurement says the line is **below this repository's working set for two
files**:

| lean worker | RSS |
|---|---|
| one sunfish/Circuit file | **1790 MB** |
| a second, concurrent | **1470 MB** |
| chain total | **3264 MB** — over the 3072 MB line |

**And there is no lever to go below two.** `lake --help` and `lake help build` on
Lake 5.0.0-src (Lean v4.33.0-rc1) were read in full: there is **no `-j`, no
`--jobs`, no parallelism option of any kind**. `LEAN_NUM_THREADS=2` caps threads
*inside* each `lean`, not the number of `lean` processes Lake starts — so a full
`lake build` here cannot be throttled below the two workers that already exceed
the cap. Attempt 2 survived only because the watchdog samples every 20 s and the
two peaks did not coincide at a sample; that is luck, not headroom.

So the line as written makes a green build **non-deterministic** for this lane
rather than bounded. Two fixes are available and both are one-line: raise the
limit to ~5 GB (still an order of magnitude under the 27 GB swap event that
prompted A11), or make the line **per-process** rather than per-chain, which is
what actually protects against a single runaway. The measurement above is offered
so the choice can be made on numbers; this lane did **not** raise its own limit
unilaterally.

### Next

R3c's interpreter half: `PyStmtTriple.forGen` at the depth-1 schedule with §14's
round as what each round runs. The calmness lane's F3c is the same shape at
depth 0 (`qs_stream.lean`, `QSRoundOK`, `qs_fold_report`); the grounds do not
overlap (§L32) but the round-classification vocabulary should be SHARED rather
than mirrored, and that is worth settling before either side states its `Inv`.

## 2026-08-22-sunfish-rtrack-2 — PROPOSAL: one round vocabulary for both folds

**Addressed to the calmness/F3c lane, and to be answered before either side
states its `Inv`.** Both lanes are about to write a fold invariant — F3c at
depth 0, R3c at depth 1 — and we already have two half-overlapping vocabularies.
Settling which is PRIMITIVE and which is DERIVED costs one exchange now and a
migration later if we skip it.

### What exists today

| name | lane | file | level |
|---|---|---|---|
| `QSRoundOK gamma value r` | calmness | `bound_depth.lean` §3 | **one round**, a four-way disjunction over the round kinds, each with its own side condition; the `searchedMove` arm is where the IH enters |
| `qsRoundOK_sound` | calmness | same | `QSRoundOK → Sound gamma value r.score` |
| `RanInv gamma value best rs` | R-track | `fold_depth1.lean` §10 | **one schedule**: `sound` (accumulator), `rounds : ∀ r ∈ rs, Sound …`, `attain` |

They are not competitors — **they are at different levels**, and that is exactly
why they should be layered rather than merged.

### The proposal, in three lines

1. **PRIMITIVE — the per-round classification.** `QSRoundOK` is it. It is the
   only place a child report enters, and it is depth-agnostic already: its four
   kinds are the fold's own branches, not QS's. **Proposed name: `RoundOK`** —
   the `QS` prefix is the one thing about it that is depth-0-flavoured, and it is
   misleading at depth 1 where the same four kinds occur. *(If the calmness lane
   would rather not pay a rename, keeping `QSRoundOK` is acceptable; the SHAPE
   decision below is what actually matters.)*
2. **DERIVED — `Sound`.** Via `roundOK_sound`, unchanged in content.
3. **SCHEDULE-LEVEL — one invariant, stated over the primitive.** `RanInv`'s
   `rounds` field should read `∀ r ∈ rs, RoundOK gamma value r` rather than
   `∀ r ∈ rs, Sound gamma value r.score`, with `Sound` recovered by (2). Then
   BOTH folds carry the same three fields over the same classification.
   **Proposed name: `FoldInv`** — `RanInv` is misnamed, because the invariant is
   not about the `ran` exit; it is the accumulator invariant that every exit
   consumes. My `fold_report_ran` is then one of its three exit corollaries, next
   to the calmness lane's `qs_fold_report_cut`.

### Where it should live

`bound_depth.lean` §3, where `QSRoundOK` already is: it is the lowest common
ancestor both `fold_depth1.lean` and `qs_stream.lean` import. This is the same
argument that just retired the duplicated `branchFalseSilent` — **the general
layer is the only place two lanes can both look.**

### What I will do if there is no objection

State R3c's `Inv` as `FoldInv` over `RoundOK`, and migrate `RanInv`'s three
lemmas (`step`, `nil`, `run`) to it in the same landing — a rename plus one field
restatement, no proof content moves. I will **not** touch `QSRoundOK`'s name
without the calmness lane's word.

### What I am asking for

One of: *agreed*, *agreed but keep `QSRoundOK`*, or *counter*. Any of the three
unblocks R3c; silence does not, because the migration cost doubles once both
`Inv`s are written against different primitives.

## 2026-08-22-sunfish-rtrack-3 — TRANSPORT CLASSIFICATION for the re-founding

Thomas ruled the monadic interpreter is THE Python interpreter and the campaign
re-proves on it rather than bridging. This entry classifies **every theorem this
lane has pushed** by what it actually depends on, so the re-founding plan can
sequence rather than survey. The axis that matters is not "old vs new" but **what
vocabulary the STATEMENT is written in** — a proof can be interpreter-heavy and
still transport untouched if its statement never mentions the interpreter.

### Class 1 — SPEC-SIDE. No interpreter, no AST. Transport UNCHANGED.

These mention only `Round`, `foldFrom`, `Report`, `Sound`, `Exit`, `Env`, `Int`.
Nothing in them can break, because nothing in them is about how a program runs.

`foldFrom_ran_no_settle`, `fold_report_ran`, `RanInv` + `.step` / `.nil` / `.run`,
`search_agrees`, `search_sound`, `settle_folds`, `settle_report`, `settle_agrees`,
`envSettle`, `envSearched`.

**This is where the shared `Inv` vocabulary with the calmness lane lives** — which
is why that proposal (entry -2) survives the re-founding intact and should still
be settled on its own timetable. `QSRoundOK`/`qs_fold_report` are class 1 too.

### Class 2 — HEAP / FRAME FACTS. Interpreter-adjacent, statement-independent.

These mention `World`, `Heap`, `Env` and nothing else. They survive any interpreter
that keeps the memory model — which the parity gate says it does.

`PstAt` + `.push` / `.append` / `.update_ne`, `valueRuns_quiet_of_pstAt` (its
CONCLUSION is `callIn`-shaped, so it is class 3 at the boundary — but the
predicate and its three stability lemmas are pure class 2 and are the reusable
part), `sbStoredAt`, `kmStored`.

**This is the class the coordinator flagged, and the reason to flag it is real:**
`PstAt` was invented precisely to move a world question out of the interpreter's
vocabulary and into the heap's. That is what makes it transport. The lesson
generalises — *an altitude lemma that names what the world contributes is
re-founding-proof, and a gate that inlines the same fact is not.*

### Class 3 — AST PINS. Depend on `Stmt`/`Expr` and on ingestion, not on execution.

`sbSearch_sharp`, `sbMoveDepth_sharp`, `sbLive_sharp`, `corrBody_split`,
`sbCorr_sharp`, `sbKillB_split`, `sbKillEvict_lit`, `sbMB_four`,
`sbKiller_test_lit`.

**Transport iff the AST and the extractor are unchanged** — they are statements
about the shipped program's shape, not about its meaning. The `*_plan` pins
(`sbNull_plan`, `sbStand_plan`, `sbKiller_plan`, `gxPlan_*`) are the EXCEPTION:
`genPlan` is the generator walker's notion, so those are class 4.

### Class 4 — INTERPRETER-BOUND. Re-prove.

Everything `execStmt`/`evalExpr`/`callIn`/`GenEmits`/`GenSilent`/`IterSteps`-shaped:

* the statement gates — `cap_line_low`, `break_fires`, `break_skips`,
  `move_depth_low`, `live_updates`, `search_line`, `settle_round`,
  `corr_skips_live`, `corr_fires`, `mate_line`, `best_line`, `store_runs_d`,
  `killer_stores`, `km_evict_dead`, `kill_fires`, `tail_runs_live`,
  `branch5_searches`, `ran_live_answers`;
* the generator chain — `GxRun`, `gx_chain`, `gx_drains`, `ord_stmt_emits_run`,
  `moves_prologue`, `moves_emits_ordered`;
* the general-layer pieces this lane lifted — `IterDrains.uncons` / `.exhausts`,
  `genSilent_branchFalse`.

**But the general-layer three are worth re-proving FIRST, not last.** Their
statements are one line each and their proofs are a single-fuel destructuring;
they are what every consumer above needs, and the technique — *instantiate a
threshold definition once, destructure the interpreter's own match, re-introduce*
— is interpreter-agnostic even though the statement is not.

### Class 5 — MEASUREMENTS. Transport by KIND, not wholesale.

The censuses are facts about the shipped program obtained THROUGH an interpreter,
and they split:

| kind | example | transports? |
|---|---|---|
| semantic answers | the exhaustion band, `bound()` = −47938 at the mate fixture, 2-node cut, 1-node settle | **yes** — the parity gate is exactly the claim that these are interpreter-independent |
| heap-size ledgers | the 176/177 decomposition, 84 + 88, the 1–25 per-step spread | **only if allocation is unchanged** — re-measure before citing |
| fuel thresholds | 32 for `pos.move`, 512 for the child, 256/128 | **no** — fuel is an interpreter artifact and every one of these must be re-measured |

**The 176/177 ledger is the one to re-run first**: it closed to the object, so if
it still closes on the new interpreter that is a strong independent check on the
new allocation strategy, and if it does not, the difference is exactly what the
re-founding changed.

### Clean edge

No new statements against the old interpreter from this entry onward. The lift
(entry above) is the last old-interpreter landing this lane makes.
