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
