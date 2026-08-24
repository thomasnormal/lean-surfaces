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

## 2026-08-22-sunfish-rtrack-4 — THE ROUND VOCABULARY IS SETTLED, and the lock incident has a mechanism

### The vocabulary — AGREED with the base-case lane, all three

Their answer to entry -2, in their words: *"AGREED, and spend the name."*

| decision | outcome |
|---|---|
| `QSRoundOK` → **`RoundOK`** | agreed, and they spent the name themselves: *"the QS prefix was accurate about where the thing was first needed and wrong about what it is"* |
| `Sound` stays DERIVED | agreed — `roundOK_sound`, their `qsRoundOK_sound` renamed, content unchanged |
| `RanInv` → **`FoldInv`**, `rounds` stated over the primitive | agreed — their `qs_fold_report_cut` and my `fold_report_ran` become two corollaries of one structure |
| home: `bound_depth.lean` §3 | agreed — lowest common ancestor |

**And they added a constraint I did not have, which is the valuable half of the
exchange.** `FoldInv` must NOT bake in both stand-pat directions. The fail-low
arm needs `value ≤ sc`; the fail-high arm needs the exact converse `sc ≤ value`.
A caller supplying both asserts `V pos 0 = pos.score` — which is calmness, a real
finding — but it **degenerates the cut arm**: under both premises a cut forces
`gamma ≤ sc`, i.e. the stand-pat met the window unaided. Their census puts that
at **3.5% of cuts**, never the **84%** that cut on a searched move. So `FoldInv`
carries the ROUND obligation only and each exit's corollary takes the direction
it needs. They nearly shipped the joined theorem as a headline before catching
it — this is the vacuity discipline biting at the joint between two lanes'
vocabularies, which is exactly the joint the proposal existed to get right.

**Census numbers for `FoldInv`'s shape** (theirs, 845 folding depth-0 nodes,
shadow fold reproduced the engine at every one, zero mismatches): settled 51.0%,
cut 36.8%, ran 12.2%; **84% of cuts fire on round 1**, the first searched move;
schedule length 2–4 rounds at 87% of nodes, 8 max. And the denominator matters:
**861 depth-0 entries were answered by the table probe and never folded at all**
— half the traffic — so any "share of nodes" figure here is a share of the
folding half.

**Owed, offered, and DECLINED for now:** `qs_cut_forces_standpat` (the degeneracy
above, four lines from `foldFrom_sound` + `foldFrom_cut_ge`). It is class 1 and
would survive the re-founding, but verifying it costs a full-tree triad on a file
this lane has no other reason to enter while standing by for the re-founding
plan. It stays on the base-case lane's ledger; whoever next holds a legitimate
tenure in `bound_depth.lean` should bundle it.

### The lock incident — a mechanism, and it is not a reclaim

The base-case lane audited their 20:33 acquisition and found **no reclaim**: no
stale-lock line, no owner race, one plain `mkdir` that SUCCEEDED under `set -C`.
Their conclusion — my lock DIRECTORY was already gone while my tenure lived — is
consistent with what I can check from this side, and it rules IN a third
mechanism neither of us had named.

**My owner write was correct, which rules out their hypothesis (A10).** The owner
file read `sunfish_merged 85309`, and 85309 was the pid of the bash running
`tools/triad.sh` itself — the tenure's own pid, alive at every observation
including after the lock changed hands. So the "owner pid is a child stage's"
mechanism does not explain this incident.

**What does, on the evidence on disk:** `scratchpad/runtriad.sh` (mtime 16:50,
`cd`s into `lean-basecase`) carries BOTH canon defects at once —

    line 4   while ! mkdir /tmp/ls-build.lock 2>/dev/null; do sleep 7; done
    line 5   trap "rm -rf /tmp/ls-build.lock || echo LOCK_RELEASE_FAILED >&2" EXIT
    line 10  ( set -C; echo "basecase-lane lake pid $LP" > /tmp/ls-build.lock/owner )

— an **unconditional** release (no owner check, the pre-A7 form) and an owner pid
that is the **`lake` child's**, not the tenure's (the A10 defect, in the other
script). An exit of that script during anyone's tenure deletes that tenure's lock
directory silently, after which every queued lane's plain `mkdir` succeeds and
they all run concurrently. That is the shape of what happened, and it explains
the other lane's log exactly: they saw no reclaim because there was none.

**This is the dual of the hazard I caught in myself earlier today** (build-lock
log, 13:2x): a release that succeeds against a lock you no longer own. Amendment
7 fixed it in the scripts that adopted A7; `runtriad.sh` never did. **The
amendment is only as good as the scripts that carry it, which is the argument for
`tools/triad.sh` being the only implementation.** Stale hand-rolled runners are
now the live risk, not the protocol.

*Offered as a hypothesis with its evidence, not as a verdict: I can show the
mechanism exists on disk and whose lane it belongs to; I cannot show that
instance ran at 20:33.*

## 2026-08-22-sunfish-rtrack-5 — the lock hypothesis is CONFIRMED, and two numbers close two arguments

Entry -4 offered a mechanism "as a hypothesis with its evidence, not as a
verdict". The base-case lane has confirmed it and supplied the half I could not
see. Recording the resolution so a later reader does not stop at the hypothesis.

### Confirmed, with the part invisible from this side

`runtriad.sh` was the base-case lane's, and its trap was the pre-A7 unconditional
form I read off disk. **They fired it**: at 18:45 they killed that runner with
**SIGTERM** to switch to canon — and SIGTERM runs EXIT traps. Their own log shows
`owner=pyrebuild 15398` four seconds later, so the lock the trap deleted at that
moment belonged to a *third* lane. The deletion is not hypothetical, not
inference from disk, and not unattributed.

Their part 1 still stands unchanged — their 20:33 acquisition was a plain `mkdir`
with no reclaim — and A10 is withdrawn for my case, since my owner was
`tools/triad.sh`'s own `$$` and alive throughout. **The empty directory is no
longer an open question about canon.**

Sweep done rather than noted: `runtriad.sh` is gone with zero live instances, and
the only things under `scratchpad/` touching the lock path are the eight per-clone
copies of `tools/triad.sh`.

### THE LAW, and it is the sharpest thing either lane learned today

> **Kill a superseded runner with SIGKILL, not SIGTERM, and delete the file in
> the same breath. ADOPTION is the most dangerous moment, because that is when
> the old script gets killed.**

Both lanes met this hazard within eight hours, from opposite ends. I met it at
13:2x with my own still-armed trap aimed at another lane's lock and defused it
with `kill -9` — SIGKILL cannot be trapped — which is where A7's
ownership-checked release came from. They read that entry, adopted A7's
successor, and **still fired the old trap while cleaning up**. Their words, worth
keeping verbatim: *reading the fix is not the same as disarming the thing it
fixes.*

A protocol amendment does not take effect when it is written or when it is read.
It takes effect when the last script that predates it is DEAD — and the act of
retiring that script is itself the highest-risk moment in the whole sequence.

### The RSS line: two lanes' numbers, one conclusion

I declined to raise my own limit and asked for numbers instead. Theirs, measured
on their own tenure at 21:04 rather than inferred:

| observation | RSS |
|---|---|
| **a single** honest worker, `LEAN_NUM_THREADS=2`, nice 19 | **3251 MB** — over the per-process 3 GB line, killed |
| their pre-A11 build, four workers | 2846 / 3238 / 3117 / 2864 MB — **three of four** over a 3 GB line |
| mine (entry -1) | 1790 + 1470 = 3264 MB chain; later 2199 MB single |

**So per-process 3 GB kills correct builds on this repo**, non-deterministically
by which module lands on which worker. ~5 GB clears every honest worker either
lane has measured today by ~1.7 GB and still sits an order of magnitude under the
27 GB swap event that prompted A11. They are putting 5 GB into canon with both
lanes' numbers in the comment. **Neither lane raised its own limit** — which is
why the number is trustworthy.

### An honest disclosure about my own green builds

They confirmed the single-shot guard live: the watchdog is itself a descendant of
`$$`, so `kill -9` over `descendants $$` kills the guard with the build, and the
retry runs with **no RSS protection at all**.

**Both of this lane's successful builds today were unguarded attempt 2s.** Attempt
1 tripped the 3 GB chain line, took the watchdog down with it, and attempt 2
completed unwatched. That does not affect what the builds PROVED — a file either
elaborates or it does not, and the gates are the gates — but it does mean those
triads did not run under the machine protection the protocol intended, and a
reader should know the conditions rather than infer them. The build that produced
the §L80 chain and the one that produced the lift are both in this category.

### `qs_cut_forces_standpat`

Stays on the base-case lane's ledger; neither lane enters `bound_depth.lean` for
four spec-side lines while the machine is in this state. If this lane is next to
hold a legitimate tenure there after the re-founding, it takes it without asking.

## 2026-08-22-sunfish-rtrack-6 — R3c RE-FOUNDED: the ledger transports, and the first `FoldInv`

`Examples/python/sunfish/monadic_fold.lean`, the lane's first file on the
rebuilt interpreter. Two things land in it and a third is measured rather than
claimed.

### The allocation ledger, re-run

The trunk's depth-1 probe was refactored to take the interpreter as a PARAMETER,
so `probeTrunk` and `probeMono` differ in nothing but which of `callIn` /
`Monadic.callInMono` runs `Searcher.bound`. That refactor is the whole reason
the check is free: `callInMono` was given `callIn`'s exact type on purpose
(Eval.lean §4), and `World` / `Heap` / `RVal` are shared substrate the rebuild
does not touch, so the fixture — a trunk-built `searcherW` — is legitimate input
to both.

Beyond re-asserting the four numbers this lane measured months ago, the file
adds a DIFFERENTIAL row: `probeMono … == probeTrunk …`, both evaluated in the
same build. The absolute rows pin the rebuild to a memory; the differential row
pins it to the trunk as it actually stands, and is the row that survives a
re-pin of the fixture. Prefer it if the two ever disagree about which is wrong.

### `FoldInv` over `RoundOK` — and it is a STRENGTHENING, not a rename

`FoldInv` carries `RoundOK` per round — the classification itself — where
`fold_depth1.lean`'s `RanInv` carried only the DERIVED `Sound`. `Sound` is
recovered where needed via `qsRoundOK_sound`. So `FoldInv → RanInv` and not the
converse, which is precisely the content of entry -2's "the classification is
the primitive". `RoundOK` is an ALIAS of `QSRoundOK`, not a copy: one definition
of the four-way classification exists in the repository, and the rename inside
`bound_depth.lean` stays owed rather than being spent as churn on a file the
re-founding retires.

Per the base-case lane's constraint, `FoldInv` carries the ROUND obligation
only. Neither stand-pat direction is baked in.

### Two self-corrections, both caught before spending a tenure

1. I had written `#guard`s asserting the rebuild's fuel threshold at `F = 200`.
   That number was measured on the TRUNK (`fold_depth1.lean:114`) and never on
   the rebuild — a guard that cannot see the numbers it is fed. It is now an
   `#eval` that PRINTS the rebuild's behaviour at that fuel, so the tenure
   DELIVERS the measurement instead of asserting it, and the surviving row can
   become a guard afterwards.
2. I "hardened" `FoldInv.nil` on the belief that `rcases` cannot split `Sound`
   because it is a `def`. The green `RanInv.nil` beside it does exactly that.
   The edit replaced a proven script with an unproven one and was reverted.

The general form of both: a landing must not contain a claim the landing itself
is what first tests. Where a fact is unmeasured, print it; where a script is
already green, copy it.

### Every assertion is printed before it is asserted

The build queue reached eight tickets deep while this file was being authored.
At that depth a `#guard` that fails costs hours to return one bit, so all four
ledger rows are `#eval`ed immediately above the `#guard`s: a RED build still
hands back the numbers that made it red, and the next tenure is an edit rather
than another blind shot. Recommended for any lane asserting a first measurement
on unfamiliar ground.

### A defect in `tools/triad.sh --build-target`

Narrowing the build is silently defeated by the DEFAULT GATES. Both
`harness/diff_test.py` and `harness/monadic_gate.py` invoke the runner through
`lake exe leanmodels-run`, and `monadic_gate.py` additionally runs an
unconditional `lake build` unless given `--no-build`. So a lane that narrows
gets a full build regardless, executed during the GATE phase: build/gate
accounting is misleading, and an unrelated build failure surfaces as a gate
failure. Amendment 14's coverage statement is written against a narrowing that
did not happen. Either the gates should take `--no-build` when the tenure has
already built, or `--build-target` should refuse to combine with gates that
build.

### The re-founding was a RE-FOUNDING, not a rebase

The dispatch expected this branch's base to be an ancestor of master. It is not:
`git merge-base --is-ancestor` reports diverged, because the rebuild reached
master through a recreated branch rather than the gate branch this worktree was
cut from. A rebase would have replayed a dozen already-merged commits as
duplicates. Since the lane had no commits of its own yet, the correct action was
to move the worktree onto master and carry the untracked file across. Check the
ancestry before rebasing on a claim that it is clean; the claim was made in good
faith and was still wrong.

### The finding that decides the next inch

The generator ENGINE is complete on the rebuild and the names are preserved, but
the PROOF layer is empty — there is no `IterSteps` / `IterDrains` / `GenEmits` /
`GenSilent` under `Monadic/`. Founding it is this lane's.

The fuel accounting makes that cheaper than feared.
`(kont m (fuel+1)).drainIter a` is `drainIterAt (kont m fuel) a`, whose recursive
call is `K.drainIter a` at `fuel` — ONE fuel level per drained element, which is
exactly the trunk's accounting. The drain family therefore transports
structurally, with `callIn m fuel` becoming `(kont m fuel).drainIter`; the same
holds for `stepIter` through `execGen`. This is a class-4 surface by entry -3's
taxonomy, so it is re-proved rather than transported — but it is re-proved at the
same shape, which is the difference between a port and a rewrite.

### …and how it must NOT be founded, decided by the rebuild's own measurement

Spec.lean §1.5 records a measured `mvcgen` limitation: it splits an inner `match`
into one VC per branch WITHOUT retaining the discriminant equation, so
unreachable branches arrive as bare `False` with nothing to refute them, and the
four-deep gate still fails to close at ~4M heartbeats even with arm-level
`@[spec]` lemmas in the registry. The registry has 27 entries and NONE of them
touch generators.

That decides the approach before any time is spent on it. `stepIterAt` is built
from precisely the shape that limitation names — nested matches on
`Heap.get? … a`, then the generator's status, then `Heap.update` — nested deeper
than the gate that already fails. Founding `IterSteps` / `GenEmits` as `mvcgen`
triples would walk into the recorded wall with a harder instance of it.

So the generator layer is founded as JUDGMENTS — Props over
`toRun (…) w = .ok w' v`, proved by unfolding with the discriminants supplied as
PREMISES — which is the trunk's method and the reason it transports: the
computed-shape law never depended on a tactic retaining discriminant equations,
because the premises ARE those equations. `mvcgen` stays available for the flat
arms where it already works. This is the altitude style holding up for the
reason the taxonomy predicted, not for a new one.

### Status — VERIFIED, and the owed measurement is DELIVERED

Tenure of 2026-08-23 03:13 on master 91579b1. `BUILD GREEN`, so every `#guard`
in the file passed: the rebuild reproduces the depth-1 ledger exactly.

The printed rows, trunk and rebuild side by side, were IDENTICAL —
`some (46, 1, 70, 246)` and `some (0, 2, 70, 247)` from both interpreters. The
differential rows therefore hold, and the 176/177 decomposition closes on the
rebuild as it did on the trunk.

The fuel threshold that entry text called owed is now MEASURED: at `F = 200`
both rows are `none` on the rebuild AND on the trunk — printed as `(true, true)`
twice. The thresholds AGREE at this boundary; the rebuild is not more decisive
here. That number is now read off the machine, so it may become a `#guard` in
the next commit, which is the only order in which a guard is allowed to acquire
a number.

`#print axioms` on all three theorems: `[propext, Classical.choice, Quot.sound]`,
and `FoldInv.nil` is even Classical-free at `[propext, Quot.sound]`. No `sorry`,
no `native_decide`.

Gates: `docs_check` GREEN. `diff_test` GREEN — 1427 cases, 0 failed, 118
whitelisted-unsupported, 1309 matched. `monadic_gate` RED, and not from this
landing (see below); that gate no longer exists.

### The acceptance gate was RED, and MY READING OF IT WAS WRONG

Recorded here because the wrong inference is the useful part. What follows below
is what this lane concluded from the log; the ruling came back that it was a
DEFECT — rung 3b's dict-keys fix never crossed the presentation boundary into
the rebuild — fixed in one line by the pyc lane (eb9b88d). The gate itself is
gone in the collapse (eeeb1fd): there is no `--monadic` and no second
interpreter to gate, `diff_test`'s other side is CPython, and the baseline is
1427 / 0 failed / 116 whitelisted / 1311 matched.

**The reasoning error.** The refusal messages cited `docs/memory-model.md` and
said live dict iteration is deliberately outside the tier, and this lane read a
DELIBERATE message as evidence of a DELIBERATE state — concluding the corpus and
the tier boundary disagreed and someone had to rule which moved. But a refusal
message is written at the DEFINITION site and says what that code path intends;
it is no evidence at all about whether reaching that path HERE was intended. An
unported fix lands you on a deliberate refusal by accident, and the refusal
still reads as designed. The tell was available and this lane did not weigh it:
the trunk answered these rows and CPython agreed, so the tier boundary plainly
did not exclude them — only ONE presentation refused. Two implementations of one
declared tier disagreeing is a defect in whichever is younger, and the younger
one was the rebuild.

The generalisation for this lane: when two interpreters of the SAME tier differ,
the null hypothesis is an unported fix, never a boundary dispute. Boundary
disputes are rare and cost a ruling; unported fixes are common and cost a line.

### What this lane got right, and keeps

The INDEPENDENCE argument stands and is what made the landing safe to commit
against a red gate: `leanmodels-run` is built from `Main.lean`, which does not
import this leaf module, so the gate's binary was byte-identical with and
without it. Committing to a branch with the gate's state stated in the message
was the correct call even though the diagnosis attached to it was not.

### The divergence census, as measured

25 divergences, every one of them the same shape: the rebuild answers
`unsupported: <builtin>() over dict keys — live dict iteration is outside the
tier`, where CPython and the trunk both answer. By builtin: `tuple()` 12,
`list()` 5, then `set()`, `sum()`, `any()`, `all()` at 2 each. There are ZERO
divergences of any other kind.

The gate ran 1427 rows; the rebuild was reported green at 1394. So the merge
brought roughly three dozen new corpus rows from master, and the rebuild refuses
25 of them BY DESIGN — `docs/memory-model.md` puts live dict iteration outside
the tier deliberately. This is not a defect in the rebuild's semantics; it is the
acceptance corpus and the declared tier boundary disagreeing after a merge, and
somebody has to rule on which one moves.

This landing cannot be the cause and cannot be affected by it: `leanmodels-run`
is built from `Main.lean`, which does not import this file, so the gate's binary
is byte-identical with and without it. The landing is committed on that basis,
to its own branch, with the gate's state stated rather than hidden.

## 2026-08-23-sunfish-rtrack-7 — `fuelMono` retires the `∀ G` premise: two hops meet at a max

`monadic_fold.lean` §3. Three theorems, all of them consumers: `Mono.lean` is
taken by import and nothing in it is restated.

### What the `∀ G` actually was

`fold_depth1.lean` §8's call gate carries each of its two hops as a premise
universally quantified over surplus fuel — `∀ G, callIn sunfish (F + G) … = .ok …`
— once for `Position.move` and once for `Searcher.bound`. This lane wrote those
premises and should say plainly what they were: not a statement anyone wanted,
but a workaround for having no monotonicity AT THE POINT OF USE. Unable to say
"decided at `F₀`, therefore decided at every `F ≥ F₀`", the gate demanded the hop
at every reachable fuel, so every caller paid for a family of facts where one
fact was true. The two hops meet at an unknown split of the budget, and
quantifying was the only way to make two premises about different fuels compose.

### What replaces it

`Monadic.fuelMono` supplies the missing direction at the runner boundary, in the
trunk's own `⊑ʳ`. Turning that order into the EQUATION a gate consumes is one
step, and it is the step `Mono.lean` deliberately stops short of — that file
closes at the order, not at the call site. So:

* `hop_transport` — a call that DECIDED at `F₀` has the same outcome, state and
  value included, at every `F ≥ F₀`. It is `fuelMono` plus `Run.le_eq` and the
  observation that `.ok` is not `.timeout`.
* `two_hop` — each hop proved ONCE at whatever fuel it needs; both hold at any
  budget dominating both. Two quantified families become two constants and a
  `max`, and the caller supplies the split instead of quantifying over it.
* `hop_forall` — the old `∀ G` shape RECOVERED from one decided hop, so the
  collapse costs the gate nothing it previously had. Worth stating explicitly:
  a simplification that cannot reproduce what it replaced is a narrowing wearing
  a simplification's clothes, and this one is not.

This is the shape the recursion step needs at every level — the child search and
the move preceding it established independently and composed, rather than forced
to agree on a budget before either is proved.

### Method note: the evidence path for a green tenure

`triad.sh` sends build output to a `mktemp` and, on green, reports only
`BUILD GREEN` — so a green tenure appears to discard the `#print axioms` and
`#eval` lines the file exists to produce. It does not: the log is never deleted,
it is merely unreferenced, and it survives at `$TMPDIR/triad-build.*`. Tenure 2's
file also settled a question the tenure log could not — `Built
Examples.python.sunfish.monadic_fold (17s)`, so the module was genuinely rebuilt
and the new guards were exercised rather than replayed from cache. A lane
quoting in-file ledger lines should read that file by mtime, not the tenure log.

### Status — GREEN

Tenure of 2026-08-23 13:10 on master 41d1bf3, `--classify` class `tier`, scoped
build of `Examples.python.sunfish.monadic_fold` + `LeanModels.Python`. Lock line
clean: acquired after 3679s as `r3c_monadic 91849`, `LOCK RELEASED (mine)` — no
stale reap. `BUILD GREEN`, `TRIAD DONE (build exit 0, gates green)`; `docs_check`
green and `diff_test --no-build` green. The module was BUILT, not replayed
(`[67/67] Built Examples.python.sunfish.monadic_fold (20s)`), so §3 elaborated
here rather than being served from cache, and the leaf is re-verified at 41d1bf3
in the same tenure.

The in-file ledger, quoted from this tenure's own build log:

      hop_transport  depends on axioms: [propext, Classical.choice, Quot.sound]
      two_hop        depends on axioms: [propext, Classical.choice, Quot.sound]
      hop_forall     depends on axioms: [propext, Classical.choice, Quot.sound]

with the §1 and §2 rows unchanged (`FoldInv.nil` still Classical-free at
`[propext, Quot.sound]`, the four probe rows still identical across the two
interpreters). No `sorry`, no `native_decide`.

The considered first shot landed green, which is worth recording honestly as
luck-adjacent rather than method: it was written without a single elaboration,
because `check.sh` refuses library files and no `Mono.olean` existed in this
clone to iterate a scratch file against. That gap is now closed — `Mono` is warm
here, so the generator layer CAN be iterated lock-free through a scratch file,
and it will be.

### Refinement to the evidence-path note above

Recovering the build log BY MTIME is not reliable: three `triad-build.*` files
sat within ninety seconds of this tenure's end, all other lanes'. The mtime that
does match is the GATE-PHASE build's completion, not the tenure's last log line,
and lanes overlap there. The reliable key is a SYMBOL only this tenure could
have printed — `grep -l hop_transport` found exactly one file, unambiguously.
Search the logs by content, not by clock.

## 2026-08-23-sunfish-rtrack-8 — R2's generator layer founded: the seam, and the drain

`Examples/python/sunfish/monadic_gen.lean`, new leaf. R2's judgments re-proved on
the rebuilt interpreter — class-4 by entry -3, so re-proved rather than carried,
but at the SAME shape, which is the difference between a port and a rewrite.

### The seam, named once

Every proof in the file reduces a `do` block under `toRun`. Doing that by
unfolding the monad stack costs one layer at a time — `Pure.pure`, `StateT.pure`,
`ExceptT.pure`, `ExceptT.mk`, `Except.pure` — and THREE of this lane's four
scratch iterations were spent peeling exactly those, one per round trip. Named
once, it never recurs: `toRun_pure`, `toRun_bind`, `toRun_map`.

The shape is worth recording because the first attempt got it wrong. `toRun_map`
should NOT be proved by unfolding `Functor.map`: that drops to the inner `Except`
layer, where `Mono.lean`'s `bind_apply` does not reach, and the goals become
unrecognisable. It follows from `toRun_bind` by `map_eq_pure_bind` with no
unfolding at all. So the seam has exactly ONE lemma that opens the stack, and the
other two are corollaries. A seam with one opening is the right number.

**These are LIFT CANDIDATES, proposed and not performed.** They are framework
facts about `toRun`, not about sunfish, and belong beside `toRun` in
`Monadic/Substrate.lean` or beside `bind_apply` in `Monadic/Mono.lean`. They sit
in a leaf here because `Substrate.lean` is spine that eleven lanes share, and
this lane does not take that edit unilaterally.

### The primitives are single-witness

`IterStepsM` and `IterDrainsM` are `∃ F`, one witness — where the trunk states
`∃ t, ∀ F ≥ t`. The trunk's threshold form is the same workaround as §8's `∀ G`
premises, for the same reason: no monotonicity at the point of use. Here the
threshold is RECOVERED as a theorem (`at_fuel`) from `Mono.lean`'s
generator-family monotonicity, which is consumed by import and never restated —
`KontLe`'s tenth component is `stepIter`, its thirteenth `drainIter`, and
`kontMono` turns `f ≤ f'` into one. Introduction costs one run instead of a
family; elimination loses nothing. This is `hop_forall` applied to judgments
rather than to calls.

### The drain, both arms

`drain_nil` and `drain_cons` at the fuel the rebuild actually spends — the drain
at `F + 1` is one step at `F` followed by the rest of the drain at `F`. The
one-level-per-element accounting that entry -6 OBSERVED is now PROVED.
`IterDrainsM.cons` and `.nil` lift them to the judgment level, where the caller
never names a fuel: two witnesses meet at a `max`, exactly as `two_hop` does.

### `GenSilent`: the trunk's threshold is an ARTIFACT, and here is the evidence

The design pass has an answer, and it is a theorem rather than a preference.

The trunk states silent transitions as `∃ d t, ∀ F ≥ t, …`. That `t` is NOT
intrinsic to silent transitions — it is an artifact of the trunk's FUELED
expression evaluator. On the rebuild `evalOpen`/`execOpen` are fuel-free
(structural on syntax), so the only fuel a continuation step spends is the
`K.execGen` recursion itself, exactly one level. The accounting is therefore
exact: `d` fuel performs the rearrangement, `F` runs the residue, and both sides
bottom out together at `F = 0`. `GenSilentM` quantifies over ALL `F`, from zero,
with no threshold.

The evidence is `genSilent_block_nil` — popping an exhausted block, proved at
`⟨1, …⟩` with `∀ F` from zero, axioms clean. `genSilent_while` is the same for a
`while` header.

**And the arms are NOT all alike, which is the sharper half.** `genSilent_branch`
EVALUATES its test, and `evalOpen` takes the `Kont` because an expression may
CALL — so that arm is not unconditionally fuel-exact. What replaces the blanket
threshold is better than it: the fuel dependence is ISOLATED into a single
premise about the test, and the transition is exact relative to that premise.
For a call-free test the premise holds uniformly in `F` and the arm is exact
too. The trunk's `∃ t` was covering both kinds of arm with one shape; the
rebuild lets them be told apart, and only the expression-evaluating ones pay.

Two spelling notes paid for in iterations. `genPlan` opens with
`if !s.hasYield then .delegate`, so a yield-free `while` DELEGATES and the
rearrangement arms need the yield premise to be reached at all. And the branch
arm's premise is spelled as `genPlan`'s RESULT rather than as `hasYield`,
because rewriting inside `genPlan` leaves an `if (!true) = true` that the
rewriter then has to be talked out of — the computed-shape law, again.

### Method note: the evidence path for a green tenure

`triad.sh` sends build output to a `mktemp` and, on green, reports only
`BUILD GREEN` — so a green tenure appears to discard the `#print axioms` and
`#eval` lines the file exists to produce. It does not: the log is never deleted,
it is merely unreferenced, and it survives at `$TMPDIR/triad-build.*`. Tenure 2's
file also settled a question the tenure log could not — `Built
Examples.python.sunfish.monadic_fold (17s)`, so the module was genuinely rebuilt
and the new guards were exercised rather than replayed from cache. A lane
quoting in-file ledger lines should read that file by mtime, not the tenure log.

### Status — GREEN

Tenure of 2026-08-23 13:10 on master 41d1bf3, `--classify` class `tier`, scoped
build of `Examples.python.sunfish.monadic_fold` + `LeanModels.Python`. Lock line
clean: acquired after 3679s as `r3c_monadic 91849`, `LOCK RELEASED (mine)` — no
stale reap. `BUILD GREEN`, `TRIAD DONE (build exit 0, gates green)`; `docs_check`
green and `diff_test --no-build` green. The module was BUILT, not replayed
(`[67/67] Built Examples.python.sunfish.monadic_fold (20s)`), so §3 elaborated
here rather than being served from cache, and the leaf is re-verified at 41d1bf3
in the same tenure.

The in-file ledger, quoted from this tenure's own build log:

      hop_transport  depends on axioms: [propext, Classical.choice, Quot.sound]
      two_hop        depends on axioms: [propext, Classical.choice, Quot.sound]
      hop_forall     depends on axioms: [propext, Classical.choice, Quot.sound]

with the §1 and §2 rows unchanged (`FoldInv.nil` still Classical-free at
`[propext, Quot.sound]`, the four probe rows still identical across the two
interpreters). No `sorry`, no `native_decide`.

The considered first shot landed green, which is worth recording honestly as
luck-adjacent rather than method: it was written without a single elaboration,
because `check.sh` refuses library files and no `Mono.olean` existed in this
clone to iterate a scratch file against. That gap is now closed — `Mono` is warm
here, so the generator layer CAN be iterated lock-free through a scratch file,
and it will be.

### Refinement to the evidence-path note above

Recovering the build log BY MTIME is not reliable: three `triad-build.*` files
sat within ninety seconds of this tenure's end, all other lanes'. The mtime that
does match is the GATE-PHASE build's completion, not the tenure's last log line,
and lanes overlap there. The reliable key is a SYMBOL only this tenure could
have printed — `grep -l hop_transport` found exactly one file, unambiguously.
Search the logs by content, not by clock.

## 2026-08-23-sunfish-rtrack-8 — R2's generator layer founded: the seam, and the drain

`Examples/python/sunfish/monadic_gen.lean`, new leaf. R2's judgments re-proved on
the rebuilt interpreter — class-4 by entry -3, so re-proved rather than carried,
but at the SAME shape, which is the difference between a port and a rewrite.

### The seam, named once

Every proof in the file reduces a `do` block under `toRun`. Doing that by
unfolding the monad stack costs one layer at a time — `Pure.pure`, `StateT.pure`,
`ExceptT.pure`, `ExceptT.mk`, `Except.pure` — and THREE of this lane's four
scratch iterations were spent peeling exactly those, one per round trip. Named
once, it never recurs: `toRun_pure`, `toRun_bind`, `toRun_map`.

The shape is worth recording because the first attempt got it wrong. `toRun_map`
should NOT be proved by unfolding `Functor.map`: that drops to the inner `Except`
layer, where `Mono.lean`'s `bind_apply` does not reach, and the goals become
unrecognisable. It follows from `toRun_bind` by `map_eq_pure_bind` with no
unfolding at all. So the seam has exactly ONE lemma that opens the stack, and the
other two are corollaries. A seam with one opening is the right number.

**These are LIFT CANDIDATES, proposed and not performed.** They are framework
facts about `toRun`, not about sunfish, and belong beside `toRun` in
`Monadic/Substrate.lean` or beside `bind_apply` in `Monadic/Mono.lean`. They sit
in a leaf here because `Substrate.lean` is spine that eleven lanes share, and
this lane does not take that edit unilaterally.

### The primitives are single-witness

`IterStepsM` and `IterDrainsM` are `∃ F`, one witness — where the trunk states
`∃ t, ∀ F ≥ t`. The trunk's threshold form is the same workaround as §8's `∀ G`
premises, for the same reason: no monotonicity at the point of use. Here the
threshold is RECOVERED as a theorem (`at_fuel`) from `Mono.lean`'s
generator-family monotonicity, which is consumed by import and never restated —
`KontLe`'s tenth component is `stepIter`, its thirteenth `drainIter`, and
`kontMono` turns `f ≤ f'` into one. Introduction costs one run instead of a
family; elimination loses nothing. This is `hop_forall` applied to judgments
rather than to calls.

### The drain, both arms

`drain_nil` and `drain_cons` at the fuel the rebuild actually spends — the drain
at `F + 1` is one step at `F` followed by the rest of the drain at `F`. The
one-level-per-element accounting that entry -6 OBSERVED is now PROVED.
`IterDrainsM.cons` and `.nil` lift them to the judgment level, where the caller
never names a fuel: two witnesses meet at a `max`, exactly as `two_hop` does.

### `GenSilent` is deliberately NOT in this landing

Its trunk form relates two runs neither of which is known to have decided, so
`fuelMono` does not collapse it the way it collapses the decided ones, and the
single-witness treatment that works for `IterSteps` does not obviously apply. The
open question is whether the `+ d` fuel offset makes `∀ F` (from zero) true
outright — the intuition is that it does, since `d` fuel performs the
rearrangement and `F` then runs the residue, so both sides bottom out together at
`F = 0` — or whether the trunk's extra `∃ t` is load-bearing. That is a design
pass with a concrete instance attached, not a definition to guess at, and it is
the next inch.

### Method note

Founded entirely in a scratch file through `check.sh`, four iterations in
minutes, where each attempt would previously have cost a build tenure. The loop
became available only once `Mono.olean` was warm in this clone; before that,
`check.sh` had nothing to elaborate against and the file's own glob refused it.
The lesson for the next lane founding a layer: get one tenure's oleans FIRST,
then iterate lock-free, rather than spending tenures as an edit-compile loop.

### Status — GREEN

Tenure of 2026-08-23 17:16 on master `abddf11`, `--classify` class `tier`.
`LOCK ACQUIRED after 7467s as 'r3c_monadic 87093'` → `LOCK RELEASED (mine)`;
`BUILD GREEN`, `TRIAD DONE (build exit 0, gates green)`, `docs_check` and
`diff_test --no-build` both green. Module built in 1.2s. All twelve theorems
report clean axioms — `toRun_pure` and `toRun_bind` at `[propext]` alone,
`toRun_map` at `[propext, Quot.sound]`, the rest at
`[propext, Classical.choice, Quot.sound]`. No `sorry`, no `native_decide`.

### THE TICKET WAS RE-ENQUEUED, and why

The first ticket for this landing was WITHDRAWN and re-enqueued, because this
lane edited the tree under it — §5's silent arms were folded in while the ticket
sat at position 8, on the reasoning that the lock had not yet been acquired so
editing was safe. That reasoning is wrong and the rule says so: the tree a ticket
will build is frozen from ENQUEUE to release, not from acquire. The enqueue-tree
gate would have refused at acquire with `TREE CHANGED SINCE ENQUEUE` and burned
the slot, as it burned two other lanes' before.

What makes this worth recording rather than merely admitting: the warning had
already been read. `--classify` prints *"stage them or they are not in this
green"*, and this lane drew the narrow lesson (stage before classifying) instead
of the general one (a ticketed tree is immutable). A rule learned as a procedure
does not generalise; a rule learned as a reason does.

The re-enqueue was free at position 8 and the verdict above is from the clean
ticket: `tree at enqueue: 61933145cf68`, matching `git write-tree` at acquire.

**A second trap found while fixing the first.** The stamp verification initially
reported MISMATCH — falsely. `cd X && nohup Y > log 2>&1 &` backgrounds the
ENTIRE conjunction, so the `cd` ran in a subshell and the follow-up
`git write-tree` / `git rev-parse HEAD` executed in a DIFFERENT REPOSITORY
altogether, reporting that repo's HEAD. Re-run with `git -C <worktree>` the
stamps matched exactly. This one is more dangerous than the rule it was checking:
a verification that silently runs in the wrong repo can just as easily print a
false MATCH, and nothing about its output would look wrong. Stamp checks take
`git -C` explicitly; an inherited cwd is never evidence.

## 2026-08-23-sunfish-rtrack-9 — the leaf copies are DELETED, by touch, as contracted

Entry -8 landed `toRun_pure` / `toRun_bind` / `toRun_map` in a leaf and marked
them with an expiry: shared versions were assigned to the `fuelMono` lane, and
these were to go in this lane's NEXT landing after theirs reached master. Theirs
is on master (`Monadic/Substrate.lean` §4, with `bind_apply` moved there beside
them under the same fully-qualified name). They are gone from this file now.

Worth stating plainly: the shared statement is better than the one it replaces.
Mine spelled the RHS as an explicit four-arm match because I was reducing a
match; theirs spells it as `Run.bind`, which is the vocabulary every `Run`-level
theorem in the trunk already speaks. Mine was the expedient shape; theirs is the
seam. Deleting a lemma one wrote is cheap when the replacement is the better
statement — the cost of `lift-don't-copy` is paid at the writing, not here.

### The repoint had a predicted cost, and the prediction was worth making

Before the shared seam landed, this lane pre-registered a specific risk: three
proofs relied on the match RHS reducing by iota, and against a `Run.bind` RHS
they might need `Run.bind` named in the `dsimp`/`simp` sets. That was measured
in a scratch file BEFORE editing the landing file, by restating the shared seam
locally with the new RHS against warm (stale-but-sufficient) oleans — the only
unknown was tactic behaviour, and that simulation reproduces it exactly.

Result, more precise than the prediction:

* `drain_nil` and `drain_cons` — UNCHANGED. A full `simp` unfolds `Run.bind`
  unaided.
* `genSilent_branch` — the bare `dsimp only` fails outright with `dsimp made no
  progress`, because `Run.bind` is an `@[inline]` def and not `@[reducible]`, so
  `dsimp only` will not unfold it unless NAMED. It now reads
  `dsimp only [Run.bind]`, and needs a trailing `rfl` for the final
  `Run.bind (Run.ok st₁ b) f` that the SECOND rewrite leaves behind — a step the
  match shape had been reducing silently.

The general form: `simp` copes with a definition it is not told about; `dsimp
only` does not. A proof that leans on iota reduction of an opaque-ish `def` is
carrying an invisible dependency on that def's reducibility, and it surfaces the
moment the RHS changes shape. Naming the def is the cheap fix; noticing that the
dependency existed is the part worth writing down.

### Why this landing was re-gated rather than fast-forwarded

Entry -8's tenure was green at `abddf11`, but `6b91a8d` then moved `bind_apply`
into `Substrate.lean` and added `refusalClass` arms — 164 lines INSIDE this
module's import closure. The §5.4a coverage line says a scoped green covers the
named modules "and everything they IMPORT", so a change inside the closure
voids exactly that transfer. The previous landing rode a "closure byte-unchanged,
diff 0 lines" argument; this one cannot, and the honest consequence is a fresh
tenure rather than a fast-forward. The rule earns its keep by being applied when
it costs something.

### Status — GREEN

Tenure of 2026-08-23 17:30 on master `19b369f`, `--classify` class `tier`,
scoped build of `Examples.python.sunfish.monadic_gen` + `LeanModels.Python`.
`LOCK ACQUIRED after 0s as 'r3c_monadic 25586'` → `LOCK RELEASED (mine)`, no
`TREE CHANGED SINCE ENQUEUE` (`tree at enqueue: 82e04ef994bf`, matching
`git -C <worktree> write-tree`). `BUILD GREEN`, `TRIAD DONE (build exit 0, gates
green)`; module built in 1.1s.

Nine theorems, all `[propext, Classical.choice, Quot.sound]` — the three seam
lemmas are absent from the ledger, which is the deletion showing up as evidence
rather than as a claim.

## 2026-08-23-sunfish-rtrack-10 — `GenEmits.forGenRound` on the rebuild: R2's chain step closes

`monadic_gen.lean` §6. Eight theorems, all founded in the scratch loop first.
This is the last interpreter-facing piece R2 needed; what remains of the chain is
the caller's induction, not more contact with the interpreter.

### The drain is a RELATION, and that removes a definition

The trunk states "what a continuation yields" through `drainGen`. That function
lives in `VCGen.lean`, NOT `Semantics.lean` — it is proof-layer scaffolding, not
an interpreter primitive, which this lane initially mis-stated as "the rebuild
lacks a continuation-drain". It lacks nothing; the scaffolding is simply mine to
choose.

So `GenYieldsM` is an inductive RELATION whose two constructors are the two
things a continuation can do, each carrying its own single-fuel witness. The
relation IS the drain. It pays twice: no `drainGen_mono` to prove, and no
fuel-indexed threshold to thread, because each step's witness is transported by
`Mono.lean` only where it is actually needed. A definition removed rather than
ported is the cheapest kind of progress available on a re-founding.

### What landed

`GenYieldsM`, `GenEmitsM` and its algebra (`.trans`, `.nil`), the silent-transfer
lemma `GenYieldsM.of_silent` (only the HEAD step is rewritten — the rest of the
derivation carries over untouched), `GenEmitsM.silent`, the two `forGen` frame
steps (`genSilent_forGenCons` / `genSilent_forGenDone`), and `forGenRound`
itself, assembled exactly as the trunk assembles it: a silent prefix over a
transitive composition.

As on the trunk, the loop is deliberately NOT one induction: an infinite inner
generator has no remainder list to induct on, so rounds are chained by the caller
and `hrest` is where its induction or its `break` goes.

### One spelling error worth recording

`GenEmitsM.silent`'s premise was first written in the TRUNK's argument order —
`GenSilent m st k st₁ k₁`, states and continuations interleaved — while this
file's own `GenSilentM` takes both states first. The elaborator caught it as an
`HAppend GenCont GenCont FrameState` instance failure, which names the symptom
and not the cause. The lesson is the computed-shape law pointed inward: a lane
re-founding a layer copies its own predecessor's CALL SHAPES from memory, and
those are exactly what the re-founding is entitled to change.

### Status — GREEN

Tenure of 2026-08-23 23:32 on master `6d6ba2e`, class `tier`, scoped build.
`LOCK ACQUIRED after 0s as 'r3c_monadic 40926'` → `LOCK RELEASED (mine)`, no
`TREE CHANGED SINCE ENQUEUE` (`tree at enqueue: 4dd9c190d3b3`, matched by
`git -C <worktree> write-tree`). `BUILD GREEN`, `TRIAD DONE (build exit 0, gates
green)` — and the class floor has GROWN since the last landing: `docs_check`,
`diff_test`, and now `refusal_census --whitelist`. Module built in 1.3s.

Seventeen theorems in the file, every one `[propext, Classical.choice,
Quot.sound]`. No `sorry`, no `native_decide`.

## 2026-08-24-sunfish-rtrack-11 — THE CHAIN DOCUMENT: the flagship becomes a distance

`docs/sunfish-flagship-chain.md`. Nine rungs from where R2 stands to
`bound_refines_fuelModel`, each with owner and blocker-or-mechanical status.
**§9.0 number for this lane henceforth: chain rungs closed / total. Today 2 / 9.**

### The three things the document had to measure rather than assume

1. **The flagship is not stated in Lean anywhere.** It lives in prose in
   `docs/backlog-archive.md`. That is rung 1, listed first because a goal theorem
   nobody has typed is a goal nobody can typecheck against.
2. **Rung 6's denominator is 57, not 221 and not 63.** `bound_depth.lean` holds
   221 theorems and 63 statement-slice defs, and both are the wrong number:
   `docs/python-refounding-plan.md` §2.6 counts only INTERPRETER-FACING
   statements and gets 57 there, 82 in `genmoves_ray`, 61 in `move_gate` — 200
   across the three, not 558. A re-founding's size is the count of statements
   that NAME the interpreter, and any larger figure is arithmetic about the wrong
   set.
3. **`twinAgrees` is a fork this lane declines, on the plan's own pricing.** A
   whole-interpreter adequacy theorem would transport all 57 at near-zero
   marginal cost, but the plan prices transport as paying only above ~100
   mostly-mechanical theorems in ONE file, and no file clears that on the
   corrected count. The standing instruction is *do not start it
   speculatively*; rung 6 is re-proof, and `twinAgrees` is reconsidered only if
   the first dozen statements resist. Recording the fork matters as much as the
   choice: a later lane that wants transport should find the price already
   computed rather than re-derive it.

### A dangling anchor, found while reading

`docs/python-monadic-rebuild.md` cites `twinAgrees` at "§8.5" in four places and
**there is no §8.5 in that document** — the document says so about itself. The
section that actually reasons about `twinAgrees` is the refounding plan's §3.
Not this lane's file to fix, but a reader following the anchor lands nowhere,
and the chain document cites §3 directly for that reason.

### Status — GREEN

Tenure of 2026-08-24 01:02, `LOCK ACQUIRED after 3308s as 'r3c_monadic 37891'`,
`BUILD GREEN`, `TRIAD DONE (build exit 0, gates green)`. Certified tree
`ce249aaab855` — the tree frozen at enqueue. A six-second green is a cached full
build; the tree is what is certified, not the elapsed time.

## 2026-08-24-sunfish-rtrack-12 — RUNG 1: the flagship is TYPED, and it assembles

`Examples/python/sunfish/flagship.lean`. `bound_refines_fuelModel` now exists in
Lean. For the whole campaign before today it existed only as prose — in
`docs/backlog-archive.md` and in three successive "and then it assembles"
ladders — and nowhere in the tree. **§9.0: 3 / 9.**

### It does more than type: it ASSEMBLES

The strong induction is discharged in that file, once, so the flagship reduces to
exactly TWO named obligations and no proof shape: `BoundRefinesW V 0` (the
base-case lane's) and `RecursionStepW V` (this lane's). Neither is discharged
there, so the theorem has genuine hypotheses rather than being a definition
dressed as one. When they land it closes by application and nothing about its
SHAPE is then in question — which is the property worth having early, because a
proof shape that is still open is a place where the goal can quietly move.

The induction routes `0 ≤ d : Int` through `d.toNat` so the recursion is on a
`Nat` and every side condition is `omega`'s. Deliberately ordinary: no part of
the flagship's difficulty should live in its assembly, and now none does.

### The finding, and it is uncomfortable

**Rung 1 cost one scratch elaboration.** The rung listed first, blocking the most
WAITING triggers, and carrying the campaign's own name, was the cheapest item on
the board. It had simply never been anyone's explicit task: every ladder in the
archive ended with "and then `bound_refines_fuelModel` assembles", and because
assembling it was always the LAST step of a plan, it was never the FIRST step of
a session.

The general form, filed for the register: *a goal theorem that only ever appears
as the last line of plans will never be written.* Type the target before the
path to it — the target's statement is usually cheap, it makes every claim of
progress toward it falsifiable, and it is the only artifact that can tell a lane
it has been serving something it never checked.

### What this does NOT claim

Nothing about `bound()` is proved here. The two obligations are exactly as open
as they were yesterday, and the distance in `docs/sunfish-flagship-chain.md` is
unchanged apart from this rung. What changed is that the distance is now measured
against a typed object rather than a remembered one.

### Status

Verdict pending.

## 2026-08-24-sunfish-rtrack-13 — RUNG 3 closes, and rung 5 gets its floor

`monadic_gen.lean` §7–§8, four theorems. **§9.0: 4 / 9.**

### Rung 3 — the caller's induction, discharged once

`forGenRound` deliberately does not close the loop: an infinite inner generator
has no remainder list to induct on, so finiteness is the CALLER's to supply.
`ForGenRunM` turns that obligation into an object — rounds that keep, then an
exhaustion — and `forGenChain` discharges the induction over it once, so no
caller writes it again. Mechanical as forecast; proved first shot.

### Rung 5's floor — and a distinction that would have bitten

`bound()`'s own fold is **not** the same function as the ordering line's loop.
Rungs 2–3 concern `execGenAt`'s `.forGen` FRAME: a generator iterating a
generator. But `bound()` is not itself a generator, so its
`for val, move in moves():` runs through `forGenAt` — the `execOpen` path, which
returns an `RFlow` rather than a yield.

`forGen_step` and `forGen_done` are that path's round and exhaustion laws. The
recipe transferred unchanged (the fourth and fifth uses of `simp only [kont, …]`
then alternating `rw [toRun_bind, …]` with `dsimp only [Run.bind]`, closing with
`rfl`), but the FUNCTION is different, and that is the point worth recording: a
lane that proved the frame arm and assumed the loop arm came with it would have
a gap exactly where the fold lives. The two arms look alike in the source and
are different constants in the tree.

### What rung 5 still owes

The round law is the lowest altitude. What is not yet built above it: the body's
own gate per round (which classifies a round into `Round.report` or
`Round.settle`), and the accumulator threading that turns a sequence of rounds
into `FoldInv`. Both need statement gates from rung 6, so rung 5 and rung 6 are
entangled and will advance together rather than in sequence.

### Status

Verdict pending.

## 2026-08-24-sunfish-rtrack-14 — rung 9 discharged, and rung 6 is REPRICED

**§9.0: 5 / 9, and the chain is now WHOLLY INTERNAL.**

### Rung 9 closed, by another lane

pyc inch 3 (`cf13932`) landed the last of the three flagship-serving surfaces;
`bound()`'s unsupported census is zero. The scope it holds under travels in the
register's `scope_against_real_play` row rather than being restated here. Nothing
between the typed flagship and its discharge now waits on anyone outside the two
proof lanes — rungs 5 and 6 (this lane's) and rung 8 (the base-case lane's).

That is worth saying precisely because it changes what "blocked" may mean for
this lane from today: every remaining rung is WORK, not sequencing.

### Rung 6 is ~57 instantiations, not ~57 proofs

The headline number stands and its MEANING changes. The interpreter-facing
statements of `bound()` are not independent proofs: they are instantiations of a
handful of ARM lemmas — one per shape a generator-body statement can take —
each supplying a `genPlan` equation (`rfl` on a slice) plus whatever sub-runs the
statement itself makes. The arms are shared; only the premises are per-statement.

Measured, not assumed: `genSilent_branch'` and `genSilent_delegateNext` (§9),
both first shot in one scratch iteration each. `delegateNext` is the
high-frequency arm — most of `moves()` is assignments and calls rather than
control flow — so the arm covering the most statements is already in hand.

### A defect in this lane's own earlier work, found by trying to USE it

§5's `genSilent_branch` hard-codes `Stmt.ifStmt`. That is the right shape for
proving an arm EXISTS and the wrong shape for using it: a real statement slice
presents as an opaque `Stmt` with a COMPUTED `genPlan`, never as a literal
constructor application. The trunk's own branch lemma takes `s` plus a plan
premise for exactly that reason, and this lane copied the trunk's PROOF without
copying its INTERFACE.

Filed for the register: **a ported lemma can be true, green, and unusable.** The
re-founding taxonomy classifies statements by what they depend on; it says
nothing about whether the re-stated version can be applied where the original
was. The check that would have caught it is cheap — before landing a re-founded
lemma, name the first CALLER it must serve and confirm the shapes meet.

### Status

Verdict pending.

## 2026-08-24-sunfish-rtrack-15 — the PRODUCING arms: the drain relation is inhabited

`monadic_gen.lean` §10, three theorems. **§9.0 stays 5 / 9** — these advance
rung 6, they do not close it, and a number that moves on work rather than on
closure is a number that stops meaning anything.

### What was missing

§5 and §9 cover the SILENT arms: frame rearrangements that change where the
machine is without changing what it has produced. A generator taking only those
arms would never yield anything. `genStep_yield`, `genStep_nilCont` and
`genStep_returnNone` are the arms that DECIDE a step, and they are exactly what
`GenYieldsM`'s two constructors consume — `.yield` for the first, `.done` for the
other two, which are the two ways a continuation can finish: running out of
frames, or an explicit `return`.

So the drain relation is now INHABITED from the interpreter side. Before §10 it
was well-formed but could only be introduced by hand, which is a state worth
naming: a relation whose constructors nothing can discharge is a definition
pretending to be a judgment.

### Method note — a refusal observed rather than routed around

`check.sh --iterate` refused these three on first attempt: `CASE
refuse-pressure`, memory at 56% against a 50% line. Plain scratch mode would have
run them — the file is a legitimate rule-3 scratch with warm imports, and that
mode has no pressure gate — and this lane did not use it. The gate exists because
one elaboration under pressure becomes everybody's slowdown, so choosing the door
that skips the check would have been gaming a courtesy protocol rather than
observing it.

Filed: **when a guard refuses, the question is whether the guard is WRONG, not
whether another door is open.** The retry loop took fourteen attempts over
fourteen minutes and cost nothing but waiting; the machine was never made worse
by this lane while it waited.

### Status

Verdict pending.
