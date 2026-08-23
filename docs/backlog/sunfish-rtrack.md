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
whitelisted-unsupported, 1309 matched. `monadic_gate` RED, and NOT from this
landing (see below).

### The acceptance gate is RED on master, and the merge is what made it so

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
