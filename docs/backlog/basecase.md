# The base-case lane's backlog

Per-lane backlog, per `docs/family-architecture.md` §9.5. **Appended only by
the base-case lane** — the calmness campaign's F-arc (`Position.move`,
`Position.rotate`, the QS measure and rank, the depth-0 fold's spec and
interpreter halves). Ids are `YYYY-MM-DD-basecase-<n>` and need no
reservation, because the lane name makes them unique.

**Everything before 2026-08-22 is in `docs/backlog.md`** and stays there; this
lane's history is §L37, §L41, §L44, §L45, §L48, §L56, §L62 (**F1 COMPLETE**),
§L64 (F2), §L65, §L73 (F3b) and §L77 (F3c inch 1), and every one of those
references keeps resolving. Migration is append-only and rewrites no history.

This lane renumbered its own section four times in one day around collisions in
the shared file (`L55→L56`, `L60→L61→L62`, `L63→L64`, `L74→L77`), which is the
§9.5 defect from the inside.

---

## 2026-08-22-basecase-1 — F3c INCH 2: the STAND-PAT ROUND, and a third loss to `/private/tmp`

§L77 put the stand-pat pair on the wire. This runs the loop body over it —
§L30's *"the round the whole fail-low `Report` argument stands on"*, gated on the
shipped statements. **F3c still does not close**; the ledger at the bottom says
what is left.

### THE LOSS, first, because it is the section's most expensive finding

This inch was written once, verified clean, and its triad ran GREEN — `lake
build` 3703 jobs, `diff_test` 1394/0, `docs_check` 75/75 — and then
`/private/tmp` purged while `script_corpus`, the LAST leg, was still running.
The clone, the file and the section draft went with it. **Everything pushed
survived; everything not pushed did not.**

That is the third loss to `/private/tmp` this campaign and the first one that was
already green. The rule the campaign carries — *push per landing* — turns out to
be weaker than what it needs to be. The sharper form:

> **Push when the thing you would have to redo becomes green, not when the
> landing is complete.** A green build and a finished triad are different events,
> and the gap between them is unbounded when the last leg is a 60-second corpus
> run behind a contended lock.

The recovery cost was ~15 minutes (re-clone, `lake exe cache get` BEFORE the
first build — 67 s against the ~5 h it saves — and a transcription of code that
was still in context). The cost had the transcript expired would have been the
whole inch. **`lake exe cache get` before the first build is not an optimisation;
it is what makes a purge recoverable at all.**

### The round nobody had gated

`sbScore` opens `if move is None and depth == 0`, and **both conjuncts hold at
exactly one round and nowhere else**: depth ≥ 1 fails the second, every real move
fails the first. `fold_depth1.lean` gates branches 2–5 — the null pass, the
mate-band value, the settle, the searched move — and never this one, because at
depth 1 it is dead. So it is proved here, from pins `bound_depth.lean` already
carried (`sbScore_lit`, `sbB1_lit`, `sbMax_lit`, `sbCut_lit`, `sbKill_lit`) and
had no consumer for.

Three statements, five gates: `standpat_score` (the `and` chain is `compare_one`
twice and `boolChain_and2` once), `standpat_max`, `standpat_cut_fires` /
`standpat_cut_skips` (two gates per `if`, §L28's law), and the two chained forms
`standpat_round_cut` / `standpat_round_next`.

### THE FINDING: the killer store dies on a different conjunct than the pin says

`sbKill_lit`'s docstring reads: *"the killer store's GATE: `move is not None` **and
`depth`** — at a QS node (`depth == 0`) the second conjunct is falsy and the store
never runs, which is what makes the depth-0 fold heap-free."*

True of a **real move** at depth 0. **Not** how it dies at the stand-pat round:
there `move` IS `None`, so `move is not None` is false and the chain
short-circuits on the FIRST conjunct — `depth` is never evaluated at all.

The consequence is a sharper theorem: **`standpat_cut_fires` needs no depth
hypothesis.** It was written with one, the unused-variable linter reported it,
and the reason it was unreferenced is this. A recorded rationale that is right
about the destination can still be wrong about the road, and **the linter is what
catches it.**

### …and the round splits where `foldFrom` splits

`standpat_agrees_cut`/`_next` close the loop to the spec: `foldFrom`'s head rule
at a `standPat sc :: rs` schedule is keyed on `gamma ≤ max best sc`, and so are
the two shipped arms. **The round lemma and `fold`'s own recursion split at the
same test** — which is what makes the `Inv` for `PyStmtTriple.forGen` writable in
the next inch: the invariant can be `foldFrom` applied to the remaining rounds
and nothing else.

`best` is deliberately left FREE in all five gates rather than fixed at
`-mateUpper`: the round lemma has to hold at every accumulator the loop can
present it with, and only the entry gate knows where the loop starts.

### Findings worth carrying

1. **Push when it goes green, not when the landing is complete.** See above.
2. **An unused hypothesis is a claim about the code, not a tidiness problem.**
   The linter warning WAS the finding.
3. **Fuel arithmetic in a composed `execStmts` is off by one, three times over.**
   `execStmts N [s₁,s₂,s₃]` peels to `execStmt (N-1) s₁`, `execStmt (N-2) s₂`,
   `execStmt (N-3) s₃`, so three gates written at `F + k` need three DIFFERENT
   instantiations of `F` against one witness. Writing the witness as a sum of the
   parts looks principled and is wrong; picking one concrete `N` and solving
   `F = N - i - k` per gate is right and takes one pass.
4. **`Env.set` towers must be spelled UNFOLDED in a `rw`.** `envStandPat e sc bst`
   and its two-`Env.set` expansion are definitionally equal but not syntactically,
   and `rw` is syntactic (§L44's rule, third appearance).

### The F3c ledger

| inch | state |
|---|---|
| 1 — the depth-0 STREAM (`moves_prologue_qs`, `moves_emits_qs`) | **DONE** (§L77) |
| 2 — the STAND-PAT ROUND (`standpat_round_cut`/`_next`) | **DONE** (this section) |
| 3 — the searched/settle rounds at depth 0 | owed — `fold_depth1.lean`'s branch gates are at depth ≥ 1 and the depth-0 caps lose their slope term |
| 4 — `PyStmtTriple.forGen` at the schedule, `Inv` = `foldFrom` on the remaining rounds; `TableAt`/`SubtreeWrites` per child | owed |

**`hfall` and `boundRefinesW_zero` wait on inch 4.** Campaign ledger: F1 done
(§L62), F2 done (§L64), F3a done (§L36), F3b done (§L73), **F3c two inches of
four**, F5 waiting on F3c.

### THE STANDING STRATEGY, adopted by touch

Five items were dispatched; this records which are **done**, which are **not
applicable**, and one that is **owed**.

1. **`tools/triad.sh` — ADOPTED, at this landing.** The lane's private script
   was killed mid-queue and replaced. Two of its defects are worth naming
   because the audit predicted them: it wrote the owner as `<lane> lake pid
   <n>` (pid NOT last — the A5 parse defect verbatim) and the pid it wrote was
   the CHILD `lake`'s, not the tenure's (the A10 defect verbatim). Both were
   written by a lane that had read the protocol, which is §7.1a's whole point.
   A third is only visible from inside: the private script's fixed 7-second
   poll **starved** — this lane queued for over an hour across four lock
   handovers while faster pollers won every race. `triad.sh`'s FIFO ticket
   queue (A9) is the fix, and starvation is the argument for it that the
   violation census could not see.
2. **Cache re-warm by `cp -Rpc` (A13) — NOT APPLICABLE, and it cost 67 s.**
   This lane re-cloned after the purge and ran `lake exe cache get` **before**
   the guidance landed. Recorded rather than skipped: the download took 67 s
   for 8 642 files, so the A13 saving over a download is real but small next
   to the ~5 h it saves over a cold build. **The load-bearing rule is
   "warm the cache before the first build", whichever way it is warmed.**
3. **Per-lane backlog — DONE.** This file. The shared file's collisions cost
   this lane four renumbers in one day.
4. **Verdict emitters conforming to §5.1 — OWED, with nothing to touch yet.**
   This lane's only instrument, `harness/qs_cut_census.py` (§L73's cut-exit
   census), was **lost in the `/private/tmp` purge before it was pushed** — the
   census's numbers survive in §L73 because they were written into the section,
   the script does not. It is re-created on next touch, conformant from the
   first line.
5. **`censuskit` — same trigger.** Adopted when the instrument is rebuilt, if
   it exists by then.

### AND A FIX TO `tools/triad.sh` ITSELF — the chain cap would have killed this build

Adopting the sanctioned script meant reading it, and it still carried the
**chain** RSS cap: `own_rss_kb()` summed every descendant and the watchdog
`kill -9`d the whole tenure when the SUM passed 3 GB. Amendment 15 had already
replaced that line with a per-process one; the script had not caught up.

This was not theoretical for this lane. Its own build, measured an hour earlier,
ran `lean` workers at **2846, 3238, 3117 and 2864 MB** — so even at the A11 cap
of `LEAN_NUM_THREADS=2`, two honest workers sum to ~6 GB and trip a 3 GB chain
cap **every time**. The queued build would have been SIGKILLed at the first
20-second watchdog tick, and the failure would have looked like a build error.

`own_rss_kb` → `own_max_rss_kb` (largest single descendant), watchdog and header
updated, `--self-test` still **12 ok, 0 failed**. The measurement is in the
comment so the next reader can see why the line is where it is.

**The general point:** "the script IS the protocol" only holds while the script
tracks the amendments. A lane adopting it inherits its lag, and the adoption
touch is the natural place to pay that down — which is what consolidation
BY TOUCH means applied to the consolidating tool itself.

### THE RE-FOUNDING, and why this inch was finished anyway

Thomas ruled mid-landing, after the rebuild's acceptance gate passed at 100 %
parity with zero divergences: *"Keep only the new versions, no reason to be
backwards compatible on anything."* The monadic interpreter becomes THE Python
interpreter; the old interpreter and the hand-rolled walker are retired by
re-founding, and the campaign's theorems are **re-proved on the new foundation,
not bridged**.

This inch was already written, verified and queued when the ruling landed, so it
was finished to a clean edge rather than abandoned: **a proved, pushed statement
is transport material, an unpushed one is nothing.** That is the same lesson the
purge taught two hours earlier, arriving from the opposite direction.

**This lane starts no new statements against the old interpreter.** What that
leaves, stated as a handoff rather than a plan:

* **Transport material, pushed and stable:** F1 (§L62 — `Position.move` end to
  end, 135 clean-axiom declarations), F2 (§L64 — `qsRank`, `RefinesAtQ`), F3b
  (§L73 — the cut exit's `Report`, `QSRoundOK`), F3c inches 1–2 (§L77 and this
  entry — the depth-0 stream and the stand-pat round).
* **Not started, and now not to be started here:** F3c inches 3–4 (the
  searched/settle rounds at depth 0, and `PyStmtTriple.forGen` at the schedule).
  The `Inv` those need is exactly what the R-track and this lane had agreed to
  settle jointly — and it now has to be settled **on the new interpreter**, so
  writing it against the old one would have been work with a known expiry.
* **The shape most likely to survive transport unchanged:** the SPEC half.
  `foldFrom`, `Report`, `Sound`, `QSRoundOK`, `fold_report_cut`,
  `qs_fold_report_*`, `qsRank` and F1's measure calculus mention no interpreter
  at all — they are statements about lists of `Round`s and about strings. The
  INTERPRETER half (every `execStmt`/`GenEmits`/∃-fuel gate) is what re-founds,
  and §L30's split into "spec half / interpreter half" turns out to have been
  the right seam for a reason nobody anticipated when it was drawn.
* **Owed on arrival:** read `docs/python-refounding-plan.md` before writing the
  next `Inv`; consume the lifted `branch_false_silent` and delete this lane's
  `branchFalseSilent` copy; re-create `harness/qs_cut_census.py` conformant to
  §5.1; adopt `censuskit` if it exists.

### AUDIT — the 20:33 acquisition, and what the path actually skipped

Asked to audit a wrongful acquisition at ~20:33 (reported as ~20:45) against the
R-track's live tenure. **The evidence does not show a reclaim, and it does show a
real hole. Both matter, so both are stated.**

**What the log proves.** `triad.log` contains **no** `STALE LOCK`, no
`reclaimed a stale lock`, no `OWNER RACE`, no `LOCK RELEASE FAILED` — the entire
acquisition is one line, `LOCK ACQUIRED after 6374s`. The path taken was a plain
`mkdir "$LOCK"` that SUCCEEDED, which means the lock directory **did not exist**
at 20:33:05. The owner write is inside that branch and runs under `set -C`, so
had an owner file been present the write would have failed and printed
`OWNER RACE`. It did not. **This lane did not remove another lane's lock and did
not clobber another lane's owner file.**

**So the directory was already gone while their tenure was alive** — and that is
the thing to explain, not the mkdir.

**The hole in canon, and it is mine to have missed too.** A8's two-part check is
wired into the RECLAIM branch only. The plain-mkdir branch has **no process-tree
check at all**: `mkdir` succeeding is treated as proof that nobody is building.
That inference is false whenever a lock directory disappears for any reason while
a build runs — and when it does, *every* queued lane acquires "correctly" and
runs concurrently. That is exactly the shape of this incident, and it is why the
aftermath needed the other lane's A7 trap to clean up. **A8 belongs on the
acquisition path, not only on the reclaim path.**

**And a second-order defect that would produce precisely a vanished directory.**
`lock_is_stale` part 2 iterates `descendants "$pid"` for a `$pid` that part 1
just proved DEAD. A dead process has no descendants — its children reparent to
`init` — so **part 2 can never veto once part 1 fires**, and the "two-part test"
collapses to one part in the only case that matters. That is the A10 shape:
an owner pid that is a child stage's, the child exits, the tenure and its `lake`
live on with `ppid 1`, and the next lane past `STALE_AFTER` reads a dead pid,
finds no descendants, and reclaims a live lock. This lane cannot prove which lane
did that here; it can prove the hole is open.

**A third, smaller one.** The `STALE_AFTER` gate is `[ "$waited" -ge "$STALE_AFTER" ]`
— the WAITER's own queue time, not the LOCK's age. Having queued 6374 s, this
lane re-ran `lock_is_stale` every 2–6 s against a lock that may have been seconds
old. Only `lock_is_stale` itself stood between that and a reclaim; with the part-2
defect above, that is a single unreliable check. **The clock should be the lock's,
not the waiter's.**

**Fixes carried into this lane's next landing** (they touch `tools/triad.sh`,
which is executing this lane's own tenure right now, so they are applied after it
closes — editing a running `bash` script is its own hazard):

1. **A8 on the acquisition path** — after `mkdir` + owner write, scan for a live
   `lake`/`lean` **not** descended from this tenure; if one exists, release and
   re-queue instead of building.
2. **The RSS guard is SINGLE-SHOT** (reported defect, confirmed by reading): the
   watchdog kills `descendants $$`, and the guard subshell **is** a descendant of
   `$$`, so it kills itself on the first trip — attempt 2 then runs unguarded.
   Fix: exclude the guard's own pid from the kill set and restart the guard per
   attempt.
3. **`STALE_AFTER` measured on the lock**, not on the waiter.
4. **`lock_is_stale` part 2** cannot stay as written; the honest repair is the
   same foreign-Lean scan as (1), since a reparented build is exactly what part 2
   is blind to.

### THE ROUND VOCABULARY — agreed, and the name is spent

Answering `docs/backlog/sunfish-rtrack.md` entry `-2`.

**Agreed, and rename it.** `QSRoundOK` → **`RoundOK`**. The `QS` prefix was
accurate about where it was first needed and wrong about what it is: its four
kinds are `sbScore`'s own branches, and nothing in the definition mentions depth.
A name that misleads at depth 1 is worse than a name that loses its provenance.

* **`Sound` stays DERIVED** via `roundOK_sound` — that is `qsRoundOK_sound`
  renamed, unchanged in content.
* **One schedule-level structure, `FoldInv`** — agreed, and the rename is right
  for the same reason: it is the accumulator invariant every exit consumes, not
  the `ran` exit's. `qs_fold_report_cut` and `fold_report_ran` become corollaries.
* **Home `bound_depth.lean` §3** — agreed, lowest common ancestor.

**Two things from this lane's side that `FoldInv` should NOT swallow** (§L73):

1. **Do not bake both stand-pat directions into it.** The fail-low arm needs
   `value ≤ sc` and the fail-high arm needs `sc ≤ value`; a caller supplying both
   asserts `V pos 0 = pos.score`, which IS calmness — and it **degenerates** the
   cut arm: under both premises a cut forces `gamma ≤ sc`, the stand-pat's own
   3.5 % of cuts, never the 84 % that cut on a searched move. `FoldInv` should
   carry the round obligation only; each exit's corollary takes the direction it
   needs.
2. **One four-line theorem is owed and unwritten** —
   `qs_cut_forces_standpat` (the degeneracy above, from `foldFrom_sound` +
   `foldFrom_cut_ge`). It was found after the build that verified §L73 had
   already compiled `bound_depth.lean`, so it was recorded as owed rather than
   claimed. It should land with whoever next touches that file.

**And confirmed on the lift:** `genSilent_branchFalse` in `VCGen.lean` is the
right home and the right name, and taking the free-module statement over the
sunfish-specialised one was the right call. This lane's pending edit to
`qs_stream.lean` predates that push and still carries the local copy, so it
resolves the conflict **in favour of the lift** at rebase.

### AUDIT, PART 2 — the mechanism was THIS LANE'S, and the R-track found it

The R-track answered the audit above with evidence this lane could not see, and
**they are right**. `scratchpad/runtriad.sh` — this lane's hand-rolled runner,
written before `tools/triad.sh` was adopted — carried the pre-A7 release:

    trap "rm -rf /tmp/ls-build.lock || echo LOCK_RELEASE_FAILED >&2" EXIT

**Unconditional. No ownership check.** Its EXIT deletes whatever lock directory
exists, whoever owns it. Its owner line was `... lake pid $LP` — the CHILD's pid,
not the tenure's, and with the pid not last: the A5 and A10 defects together.

**And this lane FIRED it.** At 18:45 the runner was killed with `SIGTERM` to
switch to canon — and `SIGTERM` runs EXIT traps. At that moment the lock belonged
to another lane (this lane's own log records `owner=pyrebuild 15398` four seconds
later). So the deletion the R-track describes is not hypothetical and not
someone else's: **this lane armed it, and this lane pulled the trigger by
cleaning up.**

What can and cannot be shown, kept apart:

* **Shown:** the trap was unconditional, it was this lane's, and killing the
  script at 18:45 fired it while another lane held the lock.
* **Not shown:** that this is what emptied the directory at 20:33. Part 1's
  finding stands unchanged — this lane's 20:33 acquisition was a plain `mkdir`
  with no reclaim — but the *cause* of the empty directory is no longer an open
  question about canon. It is this lane's script, and hypothesis (ii) in part 1
  (an A10 owner pid) is **withdrawn for this incident**: the R-track confirmed
  their owner was `$$` of `tools/triad.sh` itself and alive throughout.

**The finding that generalises, and it is theirs:** *the live risk is no longer
the protocol, it is the stale hand-rolled runners still on disk.* A7 is only as
good as the scripts that carry it, and a lane that ADOPTS canon leaves its old
runner armed — the adoption is the most dangerous moment, because that is when
the old script gets killed and its trap fires.

**Sweep, run now** (their suggestion, executed rather than noted): `runtriad.sh`
is **gone from disk with zero live instances**, and the only scripts under
`scratchpad/` that touch `/tmp/ls-build.lock` are the eight per-clone copies of
`tools/triad.sh`. **No hand-rolled runner remains on this machine.**

**The rule this lane will carry:** *kill a superseded runner with `SIGKILL`, not
`SIGTERM`, and delete the file in the same breath.* The R-track defused exactly
this hazard in themselves at 13:2x with `kill -9` — SIGKILL cannot be trapped —
and proposed what became A7. This lane read that entry, adopted A7's successor,
and still fired the old trap on the way. **Reading the fix is not the same as
disarming the thing it fixes.**

The canon fixes in part 1 stay owed regardless — (i) A8 on the acquisition path
and (ii) the single-shot RSS guard are real holes that this incident merely
did not need.

### THE RSS LINE, MEASURED — 3 GB per-process is still too low, and the guard is single-shot

Both defects fired on this lane's own tenure at 21:04, observed rather than
inferred:

    RSS KILL LINE: a single own process at 3251 MB > 3072 MB (per-process, A15)
    build exit=137
    exit 137 = RESOURCE KILL, not a red build — re-running once
    === lake build (attempt 2) ===

**1. A single HONEST `lean` worker reaches 3251 MB on the sunfish tree.** Not a
runaway — one worker, `LEAN_NUM_THREADS=2`, `nice 19`, on a tree that had built
green all day. So the A15 per-process line at 3 GB **kills correct builds on this
repository**, and it does it non-deterministically, depending on which module
lands on which worker. Earlier measurements from this lane's pre-A11 build agree:
2846 / 3238 / 3117 / 2864 MB, three of the four over a 3 GB line.

The number to choose is now on the table with evidence from two lanes. **~5 GB**
(the R-track's suggestion) clears every honest worker measured today by ~1.7 GB
and still sits an order of magnitude under the 27 GB swap event that prompted
A11. This lane did **not** raise its own limit unilaterally either; the fix goes
in canon with the measurement in the comment.

**2. The guard is SINGLE-SHOT, confirmed live.** After the kill, this tenure's
children were exactly one process — the new `lake`. The watchdog subshell is
itself a descendant of `$$`, so `for p in $(descendants $$); do kill -9` **kills
the guard along with the build.** Attempt 2 is therefore running **unguarded**,
which is the state the retry exists to avoid.

Both fixes land together: exclude the guard's own pid from the kill set, restart
the guard per attempt, and raise the line to 5 GB with these numbers recorded
beside it. Until then the retry path has no RSS protection at all — worth knowing
for any lane whose attempt 1 trips.

### What this landing contains, and its triad

**One tenure, one landing — and by the time it pushed, TWO files, not three.**

The `tools/triad.sh` fixes below were written and self-tested here, then reached
canon **ahead of this push** — the A16.1/.2/.3 work, the basename repair and the
`Cleanup` self-test cases were all already on master when this landing rebased,
propagated from this lane's peer message to the R-track rather than from its
commit. The right resolution was to drop this lane's copy and take canon's, which
is what happened. **The record below describes work this lane did; the commit
that carries it is not this one.** Worth saying plainly, because a reader
comparing the entry to the diff would otherwise find two files where the prose
promised three.

1. **`qs_stream.lean`** — F3c inch 2, the stand-pat round (`standpat_score`,
   `standpat_max`, `standpat_cut_fires`/`_skips`, `standpat_round_cut`/`_next`,
   `standpat_agrees_cut`/`_next`). Rebased onto the R-track's lift, so this
   lane's `branchFalseSilent` is **gone** and the file consumes
   `genSilent_branchFalse` from `VCGen.lean` — the duplication this lane's own
   §L77 docstring predicted would be resolved "the next time either file is
   touched", resolved by the other lane and consumed here.
2. **`docs/backlog/basecase.md`** — this file.

*(Written here, landed via canon: `tools/triad.sh` A16.1 — per-process 5 GB,
chain 10 GB, both lanes' measurements in the comment; A16.2 — the guard excludes
its own pid and restarts per attempt; A16.3 — `STALE_AFTER` on the lock's age and
A8's process-tree check on the ACQUISITION path; plus the basename repair below.
Self-test **47 ok, 0 failed**.)*

**Triad** (`tools/triad.sh --lane basecase`, verifying tenure 23:49–00:29 on the
rebased file; an earlier 20:33–21:23 tenure verified the pre-rebase form): `lake build`
**exit 0**; `docs_check` **83/83 marked blocks**, 24 illustrative-exempt;
`diff_test` **1427 cases, 0 failed**, 118 whitelisted, 1309 matched;
`script_corpus` **65 scripts, 0 failed**, 50 matched, 15 loud. No `sorry`, no
`native_decide`, no linter warning.

**And the merge does not touch this landing.** `Core.SemM` and the monadic
interpreter landed on master between this lane's build base and its push;
`git diff` over the 24 changed `.lean` files shows **none** in this file's
dependency chain (`qs_stream`, `order_genexp`, `bound_depth`, `value_bound`,
`genmoves`, `VCGen`, `GenBound`, `Semantics`, `Runtime`, `Ast`). So the green
transfers rather than being assumed to.

**One honesty note about that triad**: it ran on the PRE-rebase file — attempt 1
tripped the old 3 GB line at 21:04 and attempt 2 completed green but
**unguarded**, which is the A16.2 defect this landing fixes, biting the very
build that carries the fix. The rebase then changed `qs_stream.lean` (the lift).
So a second tenure verifies the final combination before this is pushed; a green
on a file that no longer exists in that form is not a green on what ships.

### The Inv vocabulary, settled

`RoundOK` / `roundOK_sound` / `FoldInv`, home `bound_depth.lean` §3, agreed with
the R-track in full (their entry `-2`, this lane's answer above, their `-4`/`-5`).
**The rename itself is not in this landing** and deliberately so: it belongs to
whoever next holds a legitimate tenure in `bound_depth.lean`, and after Thomas's
re-founding ruling that file's theorems are re-proved on the monadic interpreter
anyway. The vocabulary is class 1 — spec-side, no interpreter terms — so it
transports unchanged and was worth settling on its own timetable. `FoldInv`
carries **the round obligation only**, never both stand-pat directions.

### AND A16.3 CAUGHT ITSELF WITHIN THE HOUR — `C-lean-up`

The new acquisition check fired on an **idle** machine:

    FOREIGN BUILD RUNNING — lock was absent but a build is not ours; backing off (A16.3)

repeatedly, with the lock absent and **no live `lake` or `lean` anywhere**. The
detector was written as a substring glob over the executable path:

    case "$comm" in *lean*|*lake*|*gprbuild*) return 0 ;; esac

and macOS runs

    …/com.apple.MobileSoftwareUpdate.CleanupPreparePathService

**`C-lean-up`.** `*lean*` matches it, so the check refused every acquisition on a
quiet machine — a self-inflicted starvation, in a fix written to prevent
concurrent builds.

Repaired to BASENAME equality (`case "${comm##*/}" in lean|lake|gprbuild`), with
**two** self-test cases pinning both directions: the Cleanup path is ignored, a
real `…/bin/lean` is matched. **47 ok, 0 failed.**

**The same glob was already in `lock_is_stale` part 2** and is fixed with it.
There it failed SAFE — a spurious match makes a lock look live, so the error was
"never reclaim" rather than "reclaim wrongly" — which is exactly why nobody had
found it. A latent bug that only ever fails safe is invisible until someone
copies it into a place where the failure direction reverses.

**Worth keeping:** a substring match on a path is a guess about names nobody
promised you. The two guards that most needed precision were both written with
`*lean*`, and the one that mattered was found only because it broke loudly on an
idle machine an hour after it was written. §5.4's "every refusal path RUN, not
admired" is the rule that caught it: the check had a self-test, the self-test did
not cover the false-positive direction, and adding that case took one line.

---

## 2026-08-25-basecase-1 — THE BASE CASE'S OWN INDUCTION, and rung 8 was never blocked

Successor lane, predecessor transcript lost, state re-derived from the tree at
`3cc251f` (418 commits fetched; the clone was at `7c80bbc`, three days behind).
**The re-derivation is the finding**, so it is stated before the Lean.

### THE BLOCK WAS NOT REAL, and the tree says so in one grep

`docs/sunfish-flagship-chain.md` carried rung 8 — this lane's
`BoundRefinesW V 0` — as **`BLOCKED (their ledger)`**, and this lane's own §L77
successor entry agreed: *"`hfall` and `boundRefinesW_zero` wait on inch 4."*
Both were wrong, and the disagreement is checkable rather than a matter of
opinion:

* `boundRefinesW_zero` splits the base case four ways. Three arms are proved
  (`refinesAt_king_capture`, `refinesAt_probe_hit` twice) and `hfall_cut`
  discharges the fourth arm's CUT half. What remains is the **fail-low arm**.
* `basecase_depth0.lean`'s own tail says why that arm is not a leaf: at depth 0 a
  searched move recurses at depth 0 (`qs_child_depth_eq`, and §8's guards measure
  it — `bd_probe (posH 0) 40 0 = some (4, 34)`, **one call and thirty-four
  keys**), so the arm consumes a report from a depth-0 child, which is
  `BoundRefinesW V 0` itself. **Circular under an induction on depth.**
* And it names the exit in the same breath: *"what closes it is a second
  induction on the QS termination measure (calmness, not depth)."*
* **That measure has been in the tree since F2.** `qs_rank.lean` defines
  `RefinesAtQ`, `qsRank`, the descent theorem `qsRank_lt_of_qsLt` and the
  totality of the `∃ k` closure. `grep -rn RefinesAtQ Examples/` outside its own
  file returns **nothing**. It had ZERO consumers for three days.

So rung 8 waited on no artifact owned anywhere else. It waited on somebody
writing the induction that F2 was built to make writable. **The analog lane's
warning — a family table "wrong about the frontier every time it was checked
against the tree" — landed here verbatim, and it was this lane's own table.**

### WHAT LANDED — `qs_rank.lean` §5, four declarations

The base case's `flagship.lean`, and deliberately the same shape:

1. **`BoundRefinesWQ V k`** — `BoundRefinesW V 0` under a rank budget.
   Character-identical except that the conclusion is `RefinesAtQ`.
2. **`boundRefinesW_zero_of_forallQ`** — the budgets exhaust the claim, which is
   §3's closure lifted from one position to the rule.
3. **`QSRecursionStep V`** and **`boundRefinesW_zero_of_qsStep`** — the step, and
   the strong induction discharged ONCE, routed through an auxiliary
   `∀ n, ∀ k ≤ n` exactly as `flagship.lean` routes its own through `d.toNat`.
   **`BoundRefinesW V 0` is now a theorem with one hypothesis and no proof
   shape.**
4. **`refinesAt_child_of_qsStep`** — the anti-circularity result, and the reason
   the second induction is the RIGHT one: a child passing F1's own `descendsB`
   test ranks strictly below its parent, so the parent's budget strictly exceeds
   the child's rank and the hypothesis is in hand at the child. **No interpreter
   term appears in it.**
5. **`qsStep_of_hfallQ`** — the step reduced to the fail-low arm alone, and this
   is the part that is CHECKED rather than asserted: **three of the four arms
   take the induction hypothesis nowhere**, because none of them runs `moves()`.
   Only the fall-through is handed `k` and `ih`.

### THE PREDICTION, stated before the tenure

Recorded in advance per §9.0, so the measurement can contradict it:

* the section elaborates with **at most one round of fixes**;
* the split in `qsStep_of_hfallQ` is the only place where a hypothesis had to be
  moved, and the three non-fall arms need **no** change from
  `boundRefinesW_zero`'s spelling;
* the build is cheap — **nothing imports `qs_rank.lean`**, so the tenure pays for
  one module's elaboration and no downstream re-check.

### THE CLASS, and why this inch was chosen over F3c inch 3

Thomas's re-founding ruling stands: *this lane starts no new statements against
the old interpreter.* F3c inches 3–4 are the interpreter half and re-found;
§L77's handoff said so. **§5 is class 1 — spec-side.** `BoundRefinesWQ`,
`QSRecursionStep`, the induction and the child bridge mention no `execStmt`, no
`evalExpr`, no fuel: they are statements about `RefinesAt`, a `Nat` budget and a
board. They transport across the re-founding unchanged, and they were writable
today. **The seam §L30 drew — "spec half / interpreter half" — is what made a
lane with a re-founded interpreter still have something real to prove.**

### A DEBT, named at the moment it was incurred

`qsStep_of_hfallQ` **duplicates** `boundRefinesW_zero`'s four-way split. Both are
the same arithmetic on `(pos.score, lo, up, gamma)`. Factoring them apart means
editing `basecase_depth0.lean`, which `flagship.lean` consumes — so it is not
done in the landing that introduces the second consumer, and it is owed. The
honest form: a per-position `refinesAt_zero_of_fall` taking `hfall` specialised
to ONE position, of which both theorems become two-line corollaries.

### The F ladder, from the tree

F1 **DONE** (§L62), F2 **DONE** (§L64) *and now consumed for the first time*,
F3a **DONE** (§L36), F3b **DONE** (§L73), F3c inches 1–2 **DONE** (§L77,
`2026-08-22-basecase-1`), inches 3–4 **OWED and re-founding** (interpreter half),
F5 — the assembly — **is what §5 just did for everything except the fail-low
arm.**

### Rung 8, in the flagship's terms

`BoundRefinesW V 0` ⟸ `QSRecursionStep V` ⟸ `hfallQ` + `hV` + `hmateV`.
`hV` and `hmateV` are the model's, named since §L20. **`hfallQ` is the whole of
what rung 8 still owes**, and its shape is `hfall`'s with two additions: the
parent's budget, and the hypothesis at every strictly smaller one. The chain
document's rung-8 row is corrected from `BLOCKED` to `OPEN` in this landing, with
the reason recorded there.

### What this landing contains, and its triad

1. `Examples/python/sunfish/qs_rank.lean` — §5, and a header amendment so the
   file's own "what this file does NOT do" stops being false.
2. `docs/sunfish-flagship-chain.md` — the rung-8 row and its justification.
3. `docs/backlog/basecase.md` — this entry.

**Triad** (`tools/triad.sh --lane basecase`, tenure `basecase 56208`,
`LOCK ACQUIRED after 5047s` 10:49:52 → `LOCK RELEASED (mine)` 11:49:09, tree at
enqueue `0214d377b3e8`, base `3cc251f`):

* `lake build` **exit 0**, and `COVERAGE (§5.4a): full` — no target list was
  given, so the green covers every default target at this sha;
* `docs_check` **91/91 marked blocks**, 39 illustrative-exempt;
* `diff_test` **1508 cases, 0 failed**, 124 whitelisted-unsupported, 1384 matched;
* `refusal_census --whitelist` **124 rows in 51 classes**;
* `divergence_register` **OK — every row gated both ways**, 4 declared
  divergences. (This gate joined the floor on 2026-08-25; this lane's first
  tenure under it.)

No `sorry`, no `native_decide`, **no warning naming `qs_rank.lean`**, and all four
new declarations are clean-axiom — `[propext, Classical.choice, Quot.sound]` and
nothing else.

### The predictions, measured

Stated before the tenure, and all three held — the first one by a margin worth
recording:

1. *"at most one round of fixes"* — **zero.** The section elaborated first shot.
2. *"the three non-fall arms need no change from `boundRefinesW_zero`'s
   spelling"* — held; the split is character-identical but for the added budget.
3. *"the tenure pays for no downstream re-check"* — held, and the classifier
   agreed independently: it reported `--classify would build
   Examples.python.sunfish.qs_rank LeanModels.Python`. **A full tenure was queued
   anyway**, deliberately: after a 418-commit jump the stronger green is worth
   the machine time, and the floor needs `leanmodels-run` regardless. The
   coverage statement §5.4a asks for is the `full` line above.

### AND THE GREEN'S TRANSFER, checked rather than assumed

Master moved 26 commits while this tenure ran, and `git diff --name-only` over
`*.lean` shows **`pins_common.lean` in this file's dependency chain** (via
`pins_genmoves`). So the check §L73's precedent asks for was run rather than
skipped: the change is `e81dedf` *"Shard the pins pair"*, **44 insertions and
zero deletions**, and `board0` — the only name this file takes from it — is
untouched. The green therefore transfers, and a re-gate rides with the next
inch's tenure rather than being claimed here. **A purely additive dependency is
still a changed dependency; what makes this safe is the diff, not the word
"additive".**

---

## 2026-08-26-basecase-1 — THE DESCENT'S PRODUCER, and what `hfallQ` is now down to

§5 discharged the base case's own induction and left `hfallQ` as rung 8's only
obligation. It also left something smaller and sharper: `refinesAt_child_of_qsStep`
took `descendsB b b' v` as a **hypothesis**, and

    grep -rn 'descendsB' Examples/ | grep -v qs_measure.lean

returned nothing but §5's own use. **`descendsB` had no producer.** `qs_measure.lean`
states it, proves what it implies (`qsMeasure_lt_of_descendsB`), and instantiates
it on the fixture by `#guard` — nothing derived it from a move. A hypothesis
nobody can discharge is a proof that has moved rather than progressed, so this
inch discharges it.

### THE SPLIT IS THE ENGINE'S, not a convenience

`Position.value` is a `pst` delta plus a capture term, and the two arms fall out
of that shape rather than out of what was easy to prove:

* **`descendsB_plainMove`** — the QUIET arm. `pieceCount_plainMove` fixes the
  high digit and `pstTotal_plainMove` moves the low one by exactly
  `pstCell p j - pstCell p i`, which **is** the move's value. So the second
  disjunct holds as an EQUATION, not as a bound. Four lines.
* **`descendsB_plainMove_capture`** — the CAPTURE arm, and what it does *not*
  take is the finding: **no `pstTotal`, no equation relating `v` to the board at
  all.** A capture descends because a piece left the board. That is what makes
  the arm usable at the shipped `value`, whose capture term this file therefore
  never has to model — the high digit dominating (§4's `noKnightB` refutation)
  is what buys that, three sections later.
* **`refinesAt_quietChild_of_qsStep`** — the composition with §5, so the child
  bridge is *applicable* and not merely true.

**The QS floor is the engine's constant, checked and not guessed**: `QS = 40` at
`sunfish.py:163`, and at depth 0 the filter is exactly `v >= QS` because the
`or depth` disjunct is falsy. That is the `40` `descendsB` was written with.

### HOW §6 NARROWS `hfallQ` — stated in the flagship's terms

Rung 8 is `BoundRefinesW V 0` ⟸ `QSRecursionStep V` ⟸ `hfallQ` + `hV` + `hmateV`,
unchanged. What changed is `hfallQ`'s **interior**. Before §6, discharging it
needed two different kinds of thing: a fold argument, AND a reason the children
it recurses into are reachable from the induction hypothesis. **The second kind
is now gone.** For a plain QS move — quiet or capture — the child is covered, by
composition, from the parent's budget and nothing else.

So `hfallQ`'s residue is now exactly three things, and only one of them is large:

1. **The depth-0 fold's rounds** — that the rounds the loop presents ARE moves of
   this shape, with their values. Interpreter half; re-founds; the large one.
2. **The non-plain moves** — promotions, en passant, castling. `Position.move`'s
   board is `plainMoveBoard` only under `move_residue.lean`'s `PlainBoard`, so
   this residue has a predicate already written for it. Named, not hidden.
3. **The window premise** at the child, `PstInWindow (plainMoveBoard b i j)` —
   §1's side condition, discharged by the caller as it always was.

**That is the narrowing, and it is a change in KIND rather than in count.** The
circularity §L27 found — a depth-0 node's children being depth-0 nodes — is now
answered twice over: §5 said the induction can reach them, §6 says the shipped
move puts them where the induction can reach.

### The home question, decided against the instinct

`descendsB` lives in `qs_measure.lean` and the lowest-common-ancestor rule this
lane agreed for `FoldInv` would put its producer there. **The consumer decides**:
`refinesAt_child_of_qsStep` is in `qs_rank.lean`, it is the only caller, and the
LCA of the two is here. Moving it down would also have re-elaborated
`move_residue` and the 2 090-line `move_gate` for no second consumer. It moves
the moment one appears below. **LCA is a rule about the consumers a theorem
actually has, not about where its vocabulary was first defined.**

### A triangle closed, and a debt paid

`#guard plainMoveBoard board0 84 64 == d4B` (and `85 65 == e4B`). `d4B` is a
LITERAL in `faillow_census.lean` pinned to the interpreter by
`#guard ply (some (posH 0)) 84 64 == some d4Pos`; F1a's `plainMoveBoard` was
proved equal to the interpreter's `moveStr` in `move_residue.lean`. **Both edges
existed and the triangle had never been closed by a machine.** Now it is.

And §5's naming debt is paid in the same touch: the local `have hfall` inside
`refinesAt_child_of_qsStep` — which reused the campaign's most loaded name for an
unrelated rank inequality — is `hlt`. Recorded because it was recorded as owed:
a debt named in one landing and paid in the next is the cheapest kind there is.

**Still owed**: the duplicated four-way split between `qsStep_of_hfallQ` and
`boundRefinesW_zero`. Deliberately deferred again — factoring it means editing
`basecase_depth0.lean` and re-elaborating everything under it, and rung 8's
remaining work is `hfallQ`, not the split.

### THE PREDICTIONS, stated before the tenure

Per §9.0, and one of them can genuinely fail:

1. **§6 elaborates with at most one round of fixes.** The two arms are four lines
   each over lemmas whose hypotheses are already spelled; the risk is in the
   `simp only [descendsB, …]` unfolding, not in the arithmetic.
2. **The triangle closes** — `plainMoveBoard board0 84 64 == d4B` holds. This is
   the falsifiable one. Both edges are proved separately and neither was ever
   composed, so if the index conventions disagree by so much as an orientation
   this guard turns the tenure red and the finding is worth more than the green.
3. **The tenure re-gates `pins_common`'s sharding** for this file's chain, which
   `2026-08-25-basecase-1` owed and could not pay from a build base of `3cc251f`.

### What this landing contains, and its triad

1. `Examples/python/sunfish/qs_rank.lean` — §6, the `hlt` rename, and a header
   amendment so the file's own summary stays true.
2. `docs/backlog/basecase.md` — this entry.

**Triad**: ENQUEUED AND THEN CANCELLED — ticket
`1787741071577721000-81410-basecase`, 12:44:33, which had reached the HEAD of the
FIFO (`head=…-81410-basecase; owner=es 76250`) without ever acquiring. Cancelled
at 13:30 on Thomas's wind-down instruction, to free the tenure for the lanes
behind it. **So §6 IS STAGED-UNVERIFIED: no `lake build` has ever seen it.**
The re-gate this tenure was also going to pay — `2026-08-25-basecase-1`'s green
was certified at base `3cc251f` while `pins_common.lean`, in this file's chain,
was sharded underneath it — is therefore **still owed** and is the first thing
resumption should buy.


---

## 2026-08-26-basecase-2 — PARKED, indefinitely. What resumption needs and nothing else

Thomas paused the campaign to save tokens and free Lean resources. This entry is
written to be the **only** thing a successor has to read to restart this lane,
because the last handover lost its transcript and the successor had to
re-derive the frontier from the tree — which is how the "blocked" rung turned out
not to be blocked. That re-derivation is now written down instead.

### THE STATE, in one table

| thing | state | sha |
|---|---|---|
| §5 — the base case's own induction | **MERGED, green, clean-axiom** | `86ab41e` |
| §6 — the descent's producer | **STAGED, UNVERIFIED** — never built | this landing |
| rung 8 | `OPEN`, one arm: `hfallQ` | chain doc row 81 |
| chain | **5 / 9** — unchanged, and not to be advanced by this entry | — |

### RUNG 8, and it is now ONE hypothesis

    BoundRefinesW V 0  ⟸  QSRecursionStep V  ⟸  hfallQ + hV + hmateV

`hV` and `hmateV` are the MODEL's, named since §L20 and not this lane's to close.
**`hfallQ` is the whole of the remainder.** It is `hfall`'s shape plus two
additions: the parent's rank budget, and the induction hypothesis at every
strictly smaller rank.

### THE `hfallQ` RESIDUE IS THREEFOLD, and only one part is large

This is the sentence resumption should start from:

1. **The depth-0 fold's rounds** — that the rounds `bound()`'s
   `for val, move in moves():` presents ARE plain QS moves with their values.
   **This is the interpreter half, it is the big one, and it RE-FOUNDS** under
   Thomas's 2026-08-22 ruling: it must be written on the monadic interpreter, not
   the old one. Its floor already exists and is somebody else's landed work —
   `forGen_step` / `forGen_done` in `monadic_gen.lean` §8, which are the
   `forGenAt`/`execOpen` path (**not** the `execGenAt` frame arm rungs 2–3 use;
   a lane that assumes the frame arm covers the loop arm has a gap exactly where
   the fold lives). The spec side is landed too: `RoundOK` / `FoldInv` in
   `monadic_fold.lean`.
2. **The non-plain moves** — promotions, en passant, castling. `Position.move`'s
   board is `plainMoveBoard` only under `move_residue.lean`'s **`PlainBoard`**,
   which is already written. This is a named residue, not a hole.
3. **The window premise at the child** — `PstInWindow (plainMoveBoard b i j)`,
   §1's standing side condition, discharged by the caller as it always was.

### §6'S FALSIFIABLE PREDICTION, ON THE RECORD AND UNMEASURED

The staged §6 carries a guard that has **never been run**:

    #guard plainMoveBoard board0 84 64 == d4B
    #guard plainMoveBoard board0 85 65 == e4B

Both edges are proved separately and were never composed: `d4B` is a literal in
`faillow_census.lean` pinned to the interpreter by
`#guard ply (some (posH 0)) 84 64 == some d4Pos`, and `moveStr_eq_plainMoveBoard`
equates F1a's board function with the interpreter's `moveStr`. **If the index
conventions disagree by so much as an orientation, this turns the first
resumption tenure RED, and that finding is worth more than the green.** Predicted
before the park: it holds. Nobody has checked.

The other two predictions for §6, also unmeasured: it elaborates with at most one
round of fixes, and the tenure pays the `pins_common` re-gate.

### WHAT RESUMPTION SHOULD DO FIRST, in order

1. `git fetch && reset --hard origin/master`; take master's `tools/triad.sh` (the
   floor grows almost daily — it gained `divergence_register` on 08-25 and
   `backlog-index.sh --check` on 08-26, and an old copy silently runs the old
   floor).
2. **Verify `.lake` before the first build.** A warm cache is what makes a purge
   recoverable at all; `lake exe cache get` is not an optimisation. Do NOT run
   `lake` outside a tenure — other lanes' A16.3 check reads a live `lake` as a
   foreign build and backs off.
3. **Enqueue §6 unchanged and let the machine answer the triangle.** Do not
   "fix" the guard first. It is the cheapest real measurement on the board.
4. Then `hfallQ` residue item 1, monadically.

### STANDING DEBTS, carried

* **The duplicated four-way split** between `qsStep_of_hfallQ` and
  `boundRefinesW_zero`. The honest repair is a per-position
  `refinesAt_zero_of_fall` taking `hfall` specialised to ONE position, of which
  both become two-line corollaries. Deferred twice, deliberately: it means
  editing `basecase_depth0.lean` and re-elaborating everything under it including
  the 2 090-line `move_gate`, and rung 8's remaining work is `hfallQ`, not the
  split.
* **`harness/qs_cut_census.py`** — still owed, still §5.1-conformant from the
  first line when it is rebuilt. Lost to `/private/tmp` before it was ever
  pushed; §L73's numbers survive only because they were written into prose.

### THE TWO FINDINGS THIS LANE WOULD MOST LIKE KEPT

1. **A family table can be wrong about the frontier every time it is checked
   against the tree.** Rung 8 read `BLOCKED (their ledger)` for three days over a
   dependency that did not exist: the exit was a second induction on the QS rank,
   and `RefinesAtQ` had been sitting in the tree since F2 with **zero consumers**.
   `grep` settled in one command what the table had been asserting for days.
   **Re-derive the frontier from the tree, never from the document that names
   it** — including from this one.
2. **The seam between the spec half and the interpreter half is what kept this
   lane alive across a re-founding.** §L30 drew it for unrelated reasons. When
   Thomas retired the interpreter, everything class-1 — `qsRank`, `RefinesAtQ`,
   the induction, the child bridge, `descendsB`'s producer — transported
   unchanged and was writable the same day. A lane whose whole ladder had been
   interpreter-facing would have had nothing to do.
