# Backlog — the `pyrebuild` lane (the Python monadic rebuild)

Per §9.5: appended only by this lane; ids need no reservation because the
lane name makes them unique. Newest last.

---

## 2026-08-22-pyrebuild-1 — THE ACCEPTANCE GATE PASSES

**Thomas's ruling** was to rebuild the interpreter rather than debug the old
one. The rebuild is a SECOND Python semantics on the family substrate, written
in do-notation, whose acceptance test was parity with the trunk on the trunk's
own differential battery. Measured under `tools/triad.sh`, full build green:

| gate | result |
|---|---|
| `lake build` (FULL) | **green**, exit 0 |
| `docs_check` | green |
| `diff_test` (trunk baseline) | 1394 cases, 0 failed, 118 whitelisted, 1276 matched |
| `monadic_gate` | **1394 / 1394 parity (100.0 %)**, frontier 0, **divergences 0** |
| `script_corpus` trunk | 65 scripts, 0 failed, 50 matched, 15 loud |
| `script_corpus` **monadic** | 65 scripts, 0 failed, 50 matched, 15 loud |
| script rows, trunk vs monadic | **IDENTICAL row-for-row** (verdict AND file) |

The last row is the one that matters: equal TOTALS would not have proved the
same rows matched, so the comparison is per row. Oracle CPython 3.9.19; the
runner was rebuilt in this same tenure (a stale binary would have reported
pre-fix numbers — §5.4a with a build timestamp as the state).

**What the rebuild is.** `SemM W ρ = ExceptT ρ (StateT W Halt)` in
`LeanModels/Core/Outcome.lean`, shared with the family; Python's instantiation,
the `Run` isomorphism and both zoom adapters in `Python/Monadic/Substrate.lean`;
the interpreter split at the fuel boundary into a fuel-free structural half and
a fuel-structural knot; 19 `@[spec]` triples; 18 `#guard`s; two mvcgen gates.
Zero `sorry`, zero `native_decide`.

**MERGE STATUS: NOT merged.** The branch remains the rebuild's home per the
standing ruling; the merge is the coordinator's call.

### Findings this landing produced (details in docs/python-monadic-rebuild.md)

* **The recursion-knot boundary.** `Kont` was introduced as a fuel boundary and
  ended up doing four distinct jobs — fuel, a structural obstacle the measure
  could not express (the dict lockstep, kwargs values), a fuel-bounded MUTUAL
  knot (`stepIter`/`execGen`), and the script layer's shells. Anything a
  structural measure cannot express can be cut out of a recursive block through
  a defunctionalized record for the price of one field.
* **The knot must be built LAZILY.** A strict `let` makes construction O(fuel)
  PER ENTRY. It passed three green gate runs (fuel 10 000) and stalled outright
  at script mode's 10⁶. The strict version compiles, type-checks and passes
  every `#guard` — it is wrong only in COST, which no correctness gate detects.
* **A predicted defect that did not exist.** "The run retains the world/trace
  unboundedly" was written down first and refuted by measurement: 36–37 MB on
  both interpreters across three orders of magnitude of fuel.
* **Two blind instruments, both found by adding a third.** `diff_test`
  over-reports the rebuild by exactly 56 rows (it compares whitelisted rows by
  STATUS alone); `refusal_census` exits 0 on both while 66 lines of its own
  output differ. Hence `harness/monadic_gate.py`.
* **A gate is blind to what its corpus lacks.** The closed-function gate read
  1394/1394 with ZERO frontier while three arms were still `notYet` —
  unreachable from `cases.json` by construction. This is why acceptance is BOTH
  corpora, permanently, even now that both are green.
* **Three `mvcgen` defects recorded**, and the partition between them:
  `grind` wired into `mvcgen_trivial_extensible` deletes closing scripts (the
  bottom of the pipeline) but cannot help the four-deep gate, which dies inside
  mvcgen's own SPLITTING (the top). The altitude lemma that would fix it cannot
  be stated, because the splitter drops the discriminant.

### Owed

* `twinAgrees` (§8.5) — the adequacy theorem. Not attempted, not needed for the
  gate, and on the critical path for any definition swap.
* `--build-target` landed in `tools/triad.sh` with this commit (§7.1a canon).

---

## 2026-08-23-pyrebuild-2 — THE MERGE TO MASTER: one arm, 25 rows, and a dispatch discharged

Successor session to the rebuild lane (its transcript was lost; its clone,
branch and queued tenure were not). This entry records the merge payload and
the two findings the merge produced.

### The spine triad at `dc13241` — the state the fix was measured in

Queued **13362 s (3 h 42 m)** behind five lanes; tenure opened 03:53:30 and
built the full default target set in **37 minutes**, lake `4.33.0-rc1`,
`LEAN_NUM_THREADS=2`, `nice 19`.

| gate | result |
|---|---|
| `lake build` (FULL, all default targets) | **green**, exit 0 |
| `docs_check` | green |
| `diff_test` | **RED — 1427 cases: 25 failed**, 118 whitelisted-unsupported, 1284 matched |
| `script_corpus` | green — 65 scripts, 0 failed, 50 matched, 15 loud-blocked |
| `refusal_census --whitelist` | 118 rows in 46 classes |

**All 25 failures are one family**: `keys_tuple`, `keys_list_first`,
`keys_list_len`, `keys_star`, `keys_overwrite_keeps_position`, `keys_sum`,
`keys_any`, `keys_all`, `keys_set_len`, `keys_bool_int_collision`,
`keys_empty`, `star_dict`. The count was PREDICTED at 25 before the run and
came back 25.

### Finding 1 — diff_test's blindness was never a property of diff_test

Master's capability-parity audit (`8286109`) records that the differential is
*structurally blind* to this defect class, because when both sides refuse,
parity holds while both are wrong. That was true **while there were two
interpreters to compare.**

`dc13241` removed `--monadic` and made the rebuild THE interpreter. The
differential's other side is now **CPython**. The same harness, unmodified,
convicts on the same 25 rows — because the blindness was a property of
*pointing a differential at two models*, not of the instrument.

> **A differential harness is only as good as the thing on its other side.
> Two models agreeing is not evidence; the oracle is.** `8286109` states the
> rule; removing the second model is what makes the rule operational, and it
> costs no new instrument.

This is why the census's expectation column saw it first: that column was
written from CPython's measured behaviour rather than from the model's.

### Finding 2 — the Core dispatch was discharged by a branch cut before it was written

`c4f8184` ruled: *"the fix is in CORE, not in C or ES. Parameterize
`Loud.unsupported`'s payload... Until that lands, the eleven mechanical sites
converge by import and the two payload-bearing tiers HOLD."* `51b1893` then
recorded ES holding for exactly that reason.

**The branch already carried it.** `Loud.unsupported (cause : RefusalCause π)
(message : String) (snapshot : Option σ)` subsumes both holders — C at
`σ := Mem`, ES at `π := EsRefusal` — and C's never-an-observable guard is
LIFTED into Core rather than re-implemented, enforced twice structurally
(hand-written `BEq` ignores the snapshot; `observable` has nowhere to put a
`σ`). Both HOLDs become substitutions, and ES's own record predicted the
shape that landed.

The two lanes are **unblocked, not migrated** — §9.2 by-touch scheduling is
theirs. `docs/family-architecture.md` §3.4 now says so, and the claim is
pinned by a **`docs_check`-checked block** against `Core/Outcome.lean` rather
than by a prose paragraph that could rot silently (87 marked blocks, 87 ok).

### Owed, carried forward

* `twinAgrees` (§8.5) — still not attempted. Note that
  `docs/python-monadic-rebuild.md` defers to a **§8.5 that does not exist**
  in that file (three times); the only place that reasons about it is
  `docs/python-refounding-plan.md` §3.
* The deep-gate spike (`mvcgen +jp`, the `Halt` `WPMonad` `#synth`, the
  Leroy-Grall ∃F collapse probe on `genmoves_theorem.lean`). **Provenance
  caveat found while reading the pre-written probes**: `scratch/spike_jp.lean`
  is a SELF-CONTAINED replica — it redefines `Loud`/`Halt`/`SemM` locally with
  the pre-landing payload-free `Loud`, and reaches Core only by not importing
  it. Numbers taken there are claims about the replica, not about `Core.Halt`
  (§5.4a, and the twin law). `scratch/spike_probes.lean` does import Core and
  asks the real question.
* The opt-in JSON refusal-class field. Design note: `Res`/`Run` carry only a
  `msg`, so the cause must be plumbed the way `--observations` plumbs the
  world — call the inner API and keep what the public wrapper erases. It is
  not a one-line addition to `resJson`.

---

## 2026-08-23-pyrebuild-3 — THE UNION FAILED, exactly where the full build was chosen to look

### Triad #2 at `527763b`: build **RED**, and the red is the finding

Queued 1444 s; tenure 05:04:39–05:35:36. **One error in 839 targets**, and not
in anything this lane wrote:

```
LeanModels/Go/Sem.lean:249:20: Application type mismatch: The argument
  renderRefusal r.toCause π msg
has type      String
but is expected to have type   LeanModels.RefusalCause ?m.1
```

**Why no earlier green could have caught it.** Master builds Go because
master's `Loud.unsupported` still took a bare `String`. This branch built Core
because the branch had no Go tier. The defect exists **only in the union**, and
the union had never been built by either side. This landing declined
`--classify` for exactly that reason — the diff against master shows only this
lane's commits, so classification would have narrowed the build, **skipped Go,
and broken master.** The full build was chosen on that argument before the
result was known, and the result is the argument's receipt.

> **A scoped green is a claim about a scope. When two sides land payload
> changes into a shared trunk, the union is a scope neither side has ever
> built, and only the merging lane is positioned to build it.**

### The fix is in the ADOPTER, and it collapses a duplicated taxonomy

Go had re-derived §5.2 **locally** — its own `RefusalCause` with the same four
classes, and a `tag` returning byte-identical strings to Core's `className` —
then flattened cause and clause into a PREFIX (`renderRefusal`) so a scoreboard
could parse them back out of prose. That is precisely the workaround the
`RefusalCause` ruling exists to remove, and Go is the **third** tier found
doing it independently, after C's snapshot and ES's cause.

So `GoM` gains the payload it was already carrying in string form:
`SemMWith GoWorld Panic SpecRef Unit`, and `refuseGo` passes
`r.toCause.toCore π` as the cause with the rendered text unchanged as the
message. **The message is byte-identical**, so nothing downstream of the text
moves; what changes is that the cause is now DATA.

**The "one error" claim did NOT hold, and checking it is why.** `lake` stops at
the first failing module, so `Go.Sem`'s dependents were never reached.
`Go/Spec.lean:134` pins the old single-`String` `Loud` shape **by `rfl`** and
would have failed next. Two files, not one. A static census of every
Core-substrate adopter then bounded the rest: exactly **two** non-Core files
import `Core.Outcome` — Go (fixed) and Python's `Substrate.lean` (already on
the new arity). C, ES and SV are untouched because they still carry their own
`Halt`.

### The two-model window closes, and one row had to move or become a silencer

`harness/monadic_gate.py` is deleted (it compared two interpreters; there is
one). Its vocabulary retires with it: the `expect_mono` column, the `--monadic`
flag, the dead `--target trunk|monadic` option, and the `MONO_OPENED` table.

**`MONO_OPENED` could not simply be deleted.** Its own comment said the table
*"cannot become a silencer"* **because** `monadic_gate.py` adjudicated its rows
against the oracle. Deleting the adjudicator and keeping the table is exactly
how it becomes one. So its two rows were migrated in `cases.json` from
`expect: unsupported` to `expect: match` — they leave the whitelist and
`diff_test` adjudicates them against CPython. Records-vs-adjudicates is
preserved; the adjudicator changed.

Four census rows carrying `mono="MATCH"` (the inch-3a live-cursor witnesses)
had `expect="REFUSE"`, the **trunk's** answer. With one interpreter the `mono`
value is the only expectation, so they were carried over rather than dropped —
dropping them would have checked the rebuild against a retired interpreter's
expectation. Whitelist consistency after the migration is exact: **112
whitelisted rows, 112 `WHITELIST_CLASS` keys, zero stale, zero drift.**

### The static bound was WRONG, and the calibration is the useful part

Triad #3 (`4f6c11e`, build RED at 06:34:44) convicted the bound this lane
published one commit earlier: *"exactly two non-Core files import
`Core.Outcome`."* True, and irrelevant. `Examples/go/rung1/guards.lean` defines
its OWN `refusalOf` that destructures `.error (.unsupported m)` and never names
a single Core symbol, so it appears in no importer list and in no grep for the
Core API's spelling.

| measure | count |
| --- | --- |
| the published bound (DIRECT importers of `Core.Outcome`) | **2 files** |
| files TRANSITIVELY reaching `Core.Outcome` | **128 files** |
| `Loud`-shape sites outside Core (the right pattern position) | **11 lines / 3 files** |
| still broken after the Go fix | **1 root site** — `guards.lean:80` |
| errors the build reported | **6, one module** — `:80` plus five `#guard`s that fail BECAUSE it did |

Neither 2 nor 128 was the answer. The question is *"what destructures the
changed constructor?"*, and it is answered by grepping the CONSTRUCTOR's shape
— `.error (.unsupported` — not imports and not API names. That grep also
excluded two look-alikes correctly: `Circuit/Elaboration.lean` and
`Spice/Mos1Resolved.lean` use `.unsupportedDevice`, a different constructor on
a different type.

> **§5.4a's constructive half again, and this lane broke it while citing it: a
> count that prices a decision must come from the PATTERN POSITION. An import
> graph answers "who could be affected"; only the constructor's own shape
> answers "who must change".**

**A second calibration, on the instrument rather than the census.**
`triad.sh`'s failure summary is `grep -E '^error|✖' | sort -u | head -8`. The
"one error in 839 targets" reading of triad #2 came from that TRUNCATED
summary, not from the build log, and it was repeated up the chain before
anyone opened the log. #2 happened to fit under the cap; that is luck, not a
property. **The full log at `BUILD_LOG` is the source of truth, and the
summary's `head -8` should be read as a preview.** Triad #3, read from the
full log: 1 failed module, 8 error lines, **131 targets built**.

The prediction was pre-registered before #3 exited — *"`guards.lean:80` is the
only remaining break"* — and the full log confirmed it exactly: one failed
module, nothing behind it.

### Owed

* `tools/triad.sh` still pattern-matches `*monadic_gate*` in its
  runner-prebuild case (lines 691/726). Harmless — it matches nothing — but it
  names a deleted file in the SHARED build protocol. Left deliberately: a spine
  edit mid-merge is worse than a dead pattern, and it is one word for whoever
  touches that case next.

---

## 2026-08-23-pyrebuild-4 — GREEN, and the spike's headline number is VOID

The merge landed on master as `eeeb1fd`. This entry records the green it landed
on, the spike that rode inside the same tenure, and one hazard found by walking
into it.

### Triad #4 at `4c72b6c` — the gate table

| gate | result |
|---|---|
| `lake build` (all default targets) | **green**, exit 0 |
| `docs_check` | green — 87 marked blocks, 87 ok |
| `diff_test` | **1427 cases: 0 failed**, 116 whitelisted-unsupported, 1311 matched |
| `script_corpus` | green — 65 scripts, 0 failed, 50 matched, 15 loud-blocked |
| `refusal_census --whitelist` | 116 rows in 45 classes |

**Every row of the delta is accounted for**, against `dc13241`'s
`25 failed / 118 whitelisted / 1284 matched`: 1284 + 25 (the rung-3b fix) + 2
(the `MONO_OPENED` rows migrated out of the whitelist) = **1311**, and
118 − 2 = **116**. Classes 46 → 45 because `iter.dict` held exactly those two
rows. An unaccounted row would have meant the fix moved something it was not
supposed to.

**A14 coverage, stated with its state (§5.4a).** The build took **4 seconds**,
because 131 of the targets were elaborated in tenure #3 (`4f6c11e`) whose tree
differs only in `Examples/go/rung1/guards.lean` and `docs/`; #4's build is
lake's trace check confirming currency plus the rebuild of `guards` and its
dependents. The green is a true statement about all default targets on
`4c72b6c` — and it is not 131 fresh elaborations, which is the kind of thing a
later reader would otherwise assume from "full build green".

**A free cross-check, from a design this lane did not know it was using.**
`triad.sh`'s `--gates` ADDS to the floor rather than replacing it (the Ada
trap), so `docs_check` and `diff_test` each ran twice — once via the floor's
default `lake exe leanmodels-run`, once via this lane's prebuilt binary.
**Identical numbers both ways.**

### The spike — three clean answers, and one that must not be reported

| probe | `jp` | result |
|---|---|---|
| `Halt` carries `WPMonad`? | n/a | **YES** — `Except.instWPMonad`, for `Halt` AND `HaltWith String Nat` |
| snapshot guard | n/a | **kernel-verified**: three `rfl`s, exit 0 |
| `Std.Do.WP.Frames.of_wp_conjunctive` | n/a | **does not exist** in 4.33.0-rc1 |
| `Std.Do.WPMonad.of_frameClosure` | n/a | **does not exist** |
| `WPConjunctive` | n/a | **class does not exist** |
| ∃F collapse, abstract half | n/a | **PROVED**, `does not depend on any axioms` |
| ∃F collapse, monotonicity half | n/a | `Monadic.fuelMono` **unknown identifier** |
| four-deep gate, control | **false** | timeout at whnf, 1M heartbeats, 68 s |
| four-deep gate, treatment | **true** | timeout at whnf, 1M heartbeats, 76 s |

> **THE FOUR-DEEP NUMBERS ARE VOID. Both arms measured a `kont` that carries
> `sorryAx`.** `scratch/spike_jp.lean` is a SELF-CONTAINED replica of the
> substrate, and inch 3a added `GenFrame.forDict` to the tree while the replica
> kept the old match. Both files therefore emit
> `Missing cases: (List.cons (GenFrame.forDict _ _ _ _ _ _) _)` at line 1661,
> and the axiom lists say the rest:
> `'kont' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]`.
> A timeout against a sorried definition cannot be attributed to `jp`. **"+jp
> is 8 s slower and neither closes" is NOT a finding and must not be quoted as
> one.**

The replica risk was written down before the run and is now a mechanism rather
than a worry: **a probe that copies the substrate instead of importing it
measures the copy, and it goes stale at the speed of the trunk.** The owed
re-run imports the real `Monadic` modules.

**The result that IS usable is the other one.** `exf_collapse_abstract` proves,
axiom-free, that `(∃ t, ∀ F ≥ t, P F) ↔ (∃ F, P F)` for upward-closed `P`. So
the Leroy-Grall threshold form collapses **for free once monotonicity is in
hand**, and the whole question reduces to a single missing lemma —
`Monadic.fuelMono`, which SV already has as a worked shape at
`LeanModels/Sv/Obs.lean:295`. That is a very different price from "the
threshold cannot collapse", and it is the spike's real deliverable.

*(One caveat checked rather than assumed: the axiom line printed in a file that
also errored later, at the `#check`. §5.4a's trap is a `#print axioms` on a
decl whose STATEMENT failed; this theorem is at lines 20-27 with no error
reported there, and the later `#check` is an independent declaration. Judged
sound, and the owed re-run puts it in a file with no errors so the question
cannot be asked again.)*

### HAZARD — `git stash` inside a merge silently destroys `MERGE_HEAD`

Found by doing it. Run mid-merge (here, casually, to compare a block count
against the pre-merge tree), `git stash` + `git stash pop` restores the working
tree and the content is correct — **what is gone is the second PARENT.**

`git status` looks right. The diff is right. A commit at that point would have
had the correct tree and the WRONG PARENTAGE: master would not have been an
ancestor, and the failure would have surfaced much later as a push that will
not fast-forward, with nothing in the tree to explain it. It was caught only
because the commit fell through as a no-op.

> **Never stash mid-merge. If a comparison is needed, take it from
> `git show <ref>:<path>`, which touches no state.** And the check that catches
> it costs one command: `git log -1 --format=%p` on a merge commit must print
> TWO parents.

### Owed

* ~~**`Monadic.fuelMono`**~~ — **LANDED** (`LeanModels/Python/Monadic/Mono.lean`).
  Axiom-free: `'LeanModels.Python.Monadic.fuelMono' depends on axioms: [propext,
  Classical.choice, Quot.sound]`. It did NOT need the `Kont` knot opened and
  nothing was weakened: the knot is exactly where the proof splits, because the
  rebuild's own two halves induct differently — the fuel-FREE half on SYNTAX
  (`evalOpen.mutual_induct` / `execOpen.mutual_induct`, 61 arms, one uniform
  tactic) and the FUELED half on FUEL (`kontMono`, the file's one fuel
  induction, framework code like `Obs.lean`'s). `KontLe` is the fieldwise order
  on the record PLUS `K.fuel ≤ K'.fuel` — the bound is a field and the fuel-free
  half is fuel-free in its RECURSION, not in its ARGUMENTS. **The ∃F collapse is
  therefore unblocked**: `exf_collapse_abstract` + `fuelMono` is the whole
  argument, and the 8 threshold sites in `genmoves_theorem.lean` can be restated
  rather than re-proved.
* **The jp number, re-measured against the TREE** — real `Monadic` imports, no
  replica, same 1M-heartbeat budget, both arms, `jp` recorded with each.
* **The opt-in JSON refusal-class field**, via the `--observations`-style inner
  API: `Res`/`Run` carry only a `msg`, so the cause must be plumbed by calling
  the inner API and keeping what the public wrapper erases.
