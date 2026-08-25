# SystemVerilog lane — backlog

Per-lane backlog (family-architecture §9.5). Ids are `YYYY-MM-DD-sv-<n>`;
no reservation needed, the lane name makes them unique. Landings before
this file live in `docs/backlog.md` as §L60, §L67, §L68, §L84 and §L87.

---

## 2026-08-22-sv-1 — THE DETERMINISM CLAIM IS CORRECTED: the Lean was right, the PROSE overclaimed, and determinism turns out to be relative to the trace

The research survey flagged a recorded theorem of this lane as false as
stated: *"∀ schedules produce the same outcome"* holds only for race-free
designs, since IEEE 1800 leaves same-region ordering unspecified
(§4.7-4.8). **Audited. The finding is half right, and the half that is
right changes the R1 design.**

**THE LEAN WAS NEVER WRONG.** `Deterministic (d : Design) : Prop`
(`Obs.lean:646`) is a **design-indexed predicate**, and its own docstring
already reads *"`swap_nba` satisfies it, `race_blk` …"*. The tier proves
it for five designs — `adder_det`, `xsel_det`, `swap_nba_det`,
`toggle_det`, `counter_det` — and proves its **NEGATION** for the sixth:
`race_blk/proof.lean:64`, `race_blk_not_deterministic : ¬ Deterministic
raceBlkDesign`. Audited across `LeanModels/` and `Examples/`: **no
`∀ d, Deterministic d` exists and no proof consumes an unrestricted
form.** Nothing false was proved and nothing downstream rests on a bad
premise.

**THE PROSE DID OVERCLAIM, in exactly two places, and both are fixed.**
`docs/sv-charter.md` §2.4 said *"race-freedom is a theorem
(`Sv.Deterministic`) rather than an assumption"*, and its §7.1 table said
*"`Sv.Deterministic` makes race-freedom a **theorem**"*. Both invite the
reading that the tier ESTABLISHES race-freedom, which it cannot: a racy
design genuinely has no single outcome. Restated as a **per-design
obligation that is discharged or refuted, never assumed**, with the
correction left visible rather than silently patched.

**ONE REFINEMENT BACK TO THE SURVEY, because adopting its phrasing
verbatim would have been vacuous.** It asked for `RaceFree → determinism`.
But in this tier `Deterministic d` **IS** race-freedom — the same
predicate, *"all legal schedules agree on the trace"* — so
`RaceFree d → Deterministic d` would be a tautology. The correct
restatement is that the predicate is a **premise or a per-design theorem,
never a tier-wide conclusion**.

**THE SURVEY'S SECOND CHECK IS THE ONE THAT CHANGES THE DESIGN.**
Determinism quantifies over agreement of the **trace**, so its meaning
moves with the trace type: **a coarser trace makes MORE designs
deterministic.** Not abstract for R1: `sv-r1-scheduler.md` §4.3 chose
`Slot` to record `time`/`sampled`/`final` and deliberately NOT the
intermediate region states — a choice now doing double duty, because
exposing per-region states would make designs race-free *at cycle
granularity* non-deterministic *at region granularity*, since the
schedule reorders within a region by construction.

**Consequence, folded into 4a's census: the five `_det` theorems are NOT
inherited by R1.** They are statements about the cycle trace and must be
re-established through `cycleOf` — a second, independent reason the
adequacy lemma is the rung's centre rather than a formality. And
**`sampled` is the field most likely to flip a verdict**: it is genuinely
observable (clocking blocks and concurrent assertions read it), so a
design whose Preponed sample is schedule-sensitive would be
non-deterministic under R1 while deterministic today. Whether any of the
six is such a design is an R1 **check**, not an assumption — added to
inch 7's re-establishment list.

**The empirical evidence was already in this lane's harness, being read as
a curiosity rather than as data.** `race_blk_one_edge` matched
**`sigma_rev`**, not `sigma_src`: the racy design produced a *different*
trace under the reversed schedule. That is the race-free boundary showing
itself, and it is why the schedule oracle is load-bearing rather than
decorative.

### Triad

**NOT RUN — docs only, no Lean touched.** This lane still owes the
full-tree triad for `6aaeca3` (deferred under Amendment 11 at load 40.9).
No `.lake` exists in this clone — reclaimed during the disk action,
sources intact. Next ticket, in order: CoW-seed `.lake` from a warm idle
peer (A13), `tools/triad.sh`, then `Res`-bind `@[simp]` lemmas and the
stepper's subsumption proof.

---

## 2026-08-22-softfloat-3 — INBOUND FROM THE SOFTFLOAT LANE: SV lane's to triage

*Filed by the SoftFloat lane during its consumer census
(`docs/softfloat-charter.md` §2.2). Id kept in the SoftFloat namespace so this
lane mints nothing in yours.*

### `docs/family-architecture.md` §3.5.3 ATTRIBUTES A NEED TO YOU THAT NO SV DOCUMENT STATES

Line 1770 reads:

| SystemVerilog | `real`, and the divider flagship | §3.5.2 |

**Measured: no SV document asks for `real`.** `LeanModels/Sv/*.lean` contains
zero `Float`, zero `shortreal`, and every occurrence of `real` is the English
word in prose (`Ingest2.lean:642`, `Regions.lean:233`/`:331`,
`Tests.lean:15`/`:20`). The SV need this lane can find is **the divider**, and
nothing else.

**Why it matters rather than being pedantry.** SoftFloat is priced off the
consumer table. A `real` row that no tier asked for buys type-level float
support for SV's language surface — a different and much larger job than the
divider theorem — and it would be built on an inference, not a request. **If
SV does want `real`, say so and it is a real row.** If not, the correction
saves the estimate.

### AND THE FLAGSHIP'S SHAPE, AS THIS LANE UNDERSTANDS IT

Recorded so you can correct it early rather than after the spec algebra is
built around it: the target is Berkeley HardFloat's **`divSqrtRecFN`** —
division **and** square root in one RTL module — with the theorem composing
through the **`recFN` recoding** at the module boundary. Two facts from the
SoftFloat census bear on it:

* **`sqrt` does not reduce in Lean's kernel**, and floats are not the cause:
  `Nat.sqrt` is defined by well-founded recursion
  (`Init/Data/Nat/Sqrt/Basic.lean`), so `Nat.sqrt 49 = 7` fails both `rfl` and
  `decide`. `+ − × ÷` all reduce. If the divider proof needs a computable
  `√`, SoftFloat can state it by comparing squares and stay reducible — but
  that is scope this lane has flagged for Thomas
  (`docs/softfloat-charter.md` §7 item 3) and your answer is an input to it.
* The circuit side is **`LeanModels/Sv/`**, not `LeanModels/Circuit/` — and the
  trap is live: `docs/circuit-spec-surface.md` has a section headed *"Exact
  divider"* about a **resistive voltage divider**.

---

## 2026-08-23-sv-1 — THE OWED FULL-TREE TRIAD IS DISCHARGED BY SOMEONE ELSE'S GREEN, and the number carries the state it was measured in

This lane had owed a full-tree triad for its landed Lean since `6aaeca3`
(deferred under Amendment 11 at load 40.9, then a queued tenure that was
killed before it ever acquired — `grep -c 'LOCK ACQUIRED'` over its log
returns **0**, so there was never a verdict to report, only an absence).

**It is discharged, and not by an SV tenure.** `6aaeca3` is an ancestor of
`4c72b6c`, which a successor lane built FULL — all default targets, 839
jobs, green, tenure 06:36, gate floor green — and master `d41e083`'s Lean
tree is **byte-identical** to `4c72b6c`. A green over a superset tree that
contains this lane's commits unchanged is evidence about this lane's
commits.

**Recorded with its provenance rather than as a bare green**, because a
number carries the state it was measured in: *verified by the `4c72b6c`
full green (successor lane, 2026-08-23), not by an SV tenure.* This lane
never ran it, and the record should not imply otherwise.

**Consequence for the stepper tenure: it owes only its own delta.** A
scoped build extends a green rather than replacing it, so the stepper
lands under `--classify` on tier Sv with the gate floor, not a full
rebuild.

---

## 2026-08-23-sv-2 — THE STEPPER TENURE RAN AND CAME BACK RED ON ONE GOAL; the `Res` bind lemmas did their job

**Verdict, lock line first.** `LOCK ACQUIRED after 4519s as 'sv 63300'` —
75 minutes queued, then a real tenure. `build exit 0`; `docs_check` green;
`lake env lean docs/sv-step-wip.lean` **FAILED on exactly one error**;
`TRIAD DONE (build exit 0, gates RED)`; `LOCK RELEASED (mine)` — clean.

**The detachment fix is what made a tenure happen at all.** The previous
ticket was reaped as stale (base rule 5) because its pid died with the
turn. `setsid` does not exist on macOS, so the first relaunch failed
outright and never enqueued; the double-fork subshell `( nohup … & )`
reparents to init (`ppid = 1`) and survives. Ticket
`1787466441060079000-63300-sv`.

**THE FOUR `Res` BIND LEMMAS WORKED — the recorded obstacle is gone.**
§L87 named the blocker precisely: `Res`'s `Monad` bind is an anonymous
instance field, so `simp only [bind, Res.bind]` names nothing and plain
`simp` oscillates. With `bind_ok`/`bind_timeout`/`bind_unsupported`/
`pure_eq` as `@[simp]`, **the error count went 4 → 1** and every remaining
`bind`-reduction error disappeared. The diagnosis in §L87 was right and the
prescription was right.

**The one survivor was trivial and is now fixed.** At the delegating-leaf
case: `h : r.fst = st' ∧ r.2.fst = nba' ∧ r.2.snd = out'` against
`⊢ r = (st', nba', out')` — componentwise equalities on a triple that were
never destructured, so `simp_all` had nothing to substitute into. Fix:
`obtain ⟨ra, rb, rc⟩ := r` before the `simp only`. Three flagged
`unused simp argument: if_false` warnings cleaned in the same pass.

**Lemmas deliberately still OUT of `Semantics.lean`.** They are proved
`rfl` only once this gate is green; putting an unverified `rfl` inside the
`LeanModels` glob would turn `lake build` red, and **a red build means the
gates never run** — which would have cost the proof evidence as well as
the build. They move in on the landing that also moves the stepper to
`LeanModels/Sv/Step.lean`, which is the landing where classification flips
from `docs` to tier `Sv`.

**Coverage, stated rather than assumed.** This tenure's own line reads
*docs-only: NO Lean was elaborated … evidence about the prose and about
NOTHING in the model* — accurate for the class floor, and the reason the
`--gates` entry is the one carrying real information here. `--classify`
also caught, before any tenure was spent, that my edits were **unstaged and
therefore invisible** to it, that a `.lean` outside every lake glob is
still A11 Lean execution and needs `--gates`, and that
`docs/backlog/INDEX.md` was stale.

**Quality-audit §sv dispositions recorded** in
`docs/quality-audit-2026-08-23.md`: the HIGH is FIXED here; `Param.lean`'s
vacuous `crossCheck` is ACCEPTED for the next tier-`Sv` tenure (it is the
same `live`-flag law this lane landed in `sv_round_trip.py` — "clean" and
"compared nothing" must not be one value); `adder/proof.lean`'s stimulus
claim is ACCEPTED and gets reworded rather than back-filled; and the two
dangling-citation rows are ACCEPTED **PARTIAL on purpose** — they will be
corrected to say the fixtures are unreproducible pending simulator access,
because **fabricating the missing Xcelium table to satisfy a provenance
audit would be that audit's own defect one level up**.

---

## 2026-08-23-sv-3 — LANDING A: the stepper enters the build, and the gate that armed a CI bomb validates its defusal

**The stepper is in the build.** `docs/sv-step-wip.lean` →
`LeanModels/Sv/Step.lean`, imported from `LeanModels.lean`. Both `agrees`
theorems came green in tenure `sv 9282` before any of this moved, which is
why moving them is a move and not a gamble.

**AND THE FOUR `Res` LEMMAS WERE NEVER NEEDED — §L87's DIAGNOSIS WAS
WRONG, and the build caught it.** The first attempt at this landing moved
them into `Semantics.lean` and came back RED in 8 seconds:
`LeanModels/Sv/Obs.lean:67:16: 'LeanModels.Sv.Res.pure_eq' has already been
declared`. **`Obs.lean` has carried all four the whole time** —
`Res.pure_eq`, `Res.ok_bind`, `Res.timeout_bind`, `Res.unsupported_bind`,
plus a fifth this lane did not know it wanted (`Res.bind_eq_ok`, which
turns `x >>= f = .ok r` in hypothesis position into an existential nest) —
documented there as *"the do-notation stepping rules (global simp lemmas,
mirroring the Python lane's)"*.

So the recorded obstacle was never *"`Res`'s bind is an anonymous instance
field, so the lemmas do not exist"*. It was **`docs/sv-step-wip.lean`
imported `SelfCheck`, and `SelfCheck` does not import `Obs`** — the lemmas
existed, in the same namespace, one import away, and out of scope. Every
symptom §L87 recorded (`simp only [bind, Res.bind]` naming nothing, plain
`simp` oscillating) is what a missing import looks like from inside the
file. **The fix is one `import LeanModels.Sv.Obs` in `Step.lean` and three
renames to the existing spellings**; `Semantics.lean` is untouched.

This is the second time this tier has "needed" something it already had —
the first was `SelfCheck` already executing `initial` blocks. Both were
found by building rather than by reading, and both cost less than the
duplicate would have.

**`execSStmts` is RECOVERED, not superseded** — that is the whole content
of the landing. A resumable stepper and a run-to-completion walker over
the same statement type is exactly the "two interpreters, unreconciled"
shape this lane warned about in `sv-r1-scheduler.md` §9.3; the subsumption
theorem is what makes it one interpreter with a special case instead.

**THE CI BOMB, found and defused in the same landing.** `extract.py`
stamped `"version": pyslang.__version__` — the exact point release, baked
into the bytes of all 21 committed envelopes — while `.github/workflows/
ci.yml` installs pyslang **unpinned**. Harmless for as long as
`sv_round_trip` was simulator-gated and SKIPped; **armed** the moment it
became an unconditional CI step, because the next pyslang patch release
would have changed one string in every envelope and reported **all 21 as
DIVERGE on every PR**, for a reason unrelated to anyone's change. Now
stamped by FAMILY (`pyslang-11`), the same spelling `census.py` already
used, so the two instruments agree. **18 envelopes regenerated and
verified by `sv_round_trip` itself** — the gate that armed the bomb is the
gate that proves it defused: `MATCH 18 / DIVERGE 0 / REFUSE 3 / TIMEOUT 0`,
18 live of 21.

**Three envelopes deliberately still carry the old stamp.** `alu_div`,
`ff_one` and `popcnt` record `source_files` as absolute paths into a
machine that no longer exists, so nobody can regenerate them; they are
`REFUSE sources-not-in-tree`, **live=false**, and their bytes are never
compared. Left untouched rather than hand-edited, **because editing them
would make them look regenerated when they cannot be** — the schema doc
says so explicitly rather than leaving a reader to wonder why three files
differ.

**The audit's VACUOUS row is fixed, additively.** `PDesign.crossCheck`
skipped every field whose `resolved?` metadata was absent and returned
`[]`, so `[]` meant both "everything agreed" and "nothing was compared" —
an envelope with no metadata passed the *ingestion-time differential test*
without one comparison. `crossCheckFull` now pairs the messages with a
count of comparisons made, and `load_design_sv2` **refuses VACUOUS at
zero**. Done additively — `crossCheck` keeps its signature, so every
existing `#guard … == []` keeps its meaning — because changing the return
type would have broken five guards across three files for no gain. It is
the same law as the `live` flag in `sv_round_trip.py`: **a vacuous run
must not serialize as agreement**, and this lane has now applied it to
both of its differential instruments.

**One process note worth keeping.** The first regeneration loop reported
`regenerated=0` and I nearly recorded that as a finding; it was `&&`
swallowing the failure. Re-run with the error surfaced, the extractor was
failing **loudly** with `KeyError: 'version'` — two consumption sites still
read the old key. The extractor refusing rather than silently emitting a
half-updated stamp is the never-hide-errors law paying out; my loop hiding
it was the same law being broken one level up, in the same minute.

---

## 2026-08-23-sv-4 — LANDING B (4a-0): the SV tier joins the family substrate, and both adoptions are `rfl`

`LeanModels/Sv/World.lean` instantiates the four pieces §3.4 asks every
tier for. **No semantics** — no `slotStep`, no `runRegion`; this is the
plumbing those get written against.

| piece | SV |
| --- | --- |
| `W` | `SvWorld` — process table, per-region ready sets, both NBA buffers, time wheel, `$display` output, oracle counter |
| `ρ` | `Finish` (`$finish`/`$stop`) — **state-PRESERVING** |
| `π` | `SvClause` — a citation into IEEE 1800, never a quote |
| `σ` | `Unit` — no diagnostic snapshot yet |

`abbrev SvM := SemMWith SvWorld Finish SvClause Unit`.

**`ρ` is not `Loud`, and that is load-bearing.** `SvWorld.out` holds the
`$display` text, which for **97% of the corpus IS the verdict** — the
`PASS`/`FAIL` line. A `Loud` halt discards the world; `ExceptT ρ` keeps
it. Putting `$finish` in the wrong layer would silently throw away the
answer the run exists to produce.

**`orderDependence` is SV's cause, and it was already waiting.** The
family's four causes arrived in `Core` from ES, Go and Python; the one
this tier's taxonomy predicted it would need — same-region ordering the
standard leaves free (§4.7-4.8) — is exactly `orderDependence`.
`SvRefusal.race` maps onto it.

**And what is deliberately NOT a refusal: x-propagation.** Four-state
unknown is a **value**. `lx`/`lz` flow through the `LVec` operators by
tabulated per-operator rules, never short-circuit, and an x-carrying
result is a *successful* run. Modelling x in the `ExceptT` layer — natural
enough, since "unknown" reads like "exceptional" — would convert 4-state
semantics into 2-state-plus-errors. Written into the file so the next
reader cannot make that move by accident.

**Both adoption facts are `rfl`, which is the point.**
`Res.le_iff_flatLe : x ⊑ y ↔ FlatLe .timeout x y` makes SV the third
`FlatLe` instance **by iff**, keeping `Res.le`'s spelling and its `⊑`
notation, per the `Python/Obs.lean` precedent. `Res.le` carries this
tier's fuel-monotonicity ladder (`evalExpr_le` → … → `run_le`), so the iff
makes the adoption free where a rename would have re-opened every one of
those proofs.

**§9.0 — the tier's standing number, from this entry on.**

  * **envelopes: 18 live / 21 total.** The three not-live are `alu_div`,
    `ff_one`, `popcnt`, whose `source_files` are absolute paths into a
    machine that no longer exists; they are `REFUSE sources-not-in-tree`
    and never byte-compared. *Live* is the honest denominator, because a
    vacuous row must not read as agreement.
  * **stepper construct coverage: 11/11 `SStmt` constructors.** Five are
    matched explicitly in `stepSStmt` — `ifStmt` and `block` recurse
    because a nested statement may suspend, and `delay`/`waitEvent`/
    `waitCond` are the suspension points themselves. The other six
    (`m0`, `assign`, `localDecl`, `sysCall`, `finish`, `skip`) reach
    `execSStmt` through the single delegating arm, which is *why* they
    cannot drift: they are not reimplemented, they are forwarded, and
    `stepSStmts_done_agrees` proves the forwarding agrees.

**A SECOND missing import, same class as Landing A's, caught by the same
guard.** Landing B's first tenure died on
`World.lean:140: Unknown identifier 'Region'` — `Region` lives in
`Regions.lean`, and nothing in `World`'s chain reaches it
(`Step → SelfCheck/Obs → Semantics → Ast`). One import. Two things worth
keeping: the error was **loud** only because `set_option autoImplicit
false` is set in that file — without it Lean would have silently bound
`Region` as an implicit universe variable and failed later and stranger,
which is exactly what happened to `Edge` before that guard existed. And
the clash check does not catch this class, so the pre-flight now has a
second half: an **import-reachability check** that resolves every
capitalized identifier a new file uses to its defining module and
confirms that module is in the file's import closure. Run on the fixed
`World.lean` it reports one hit, `SpecRef`, which is a false positive
from a docstring mentioning Go's model — the check needs comment
stripping, noted.

**The pre-flight clash check paid for itself twice in one landing.**
Landing A's red was `Res.pure_eq has already been declared`; running the
same check *before* ticketing this time caught **`Res.timeout_le`, which
`Obs.lean:258` already declares** — the identical trap, one tenure earlier
than it would otherwise have cost. It also showed `Res.le_iff_flatLe`
exists in `LeanModels/Python/Obs.lean` and is **not** a collision, because
`Sv.Res` and `Python.Res` are different types; that is the precedent, not
a conflict. `Obs.lean`'s `timeout_le` and `⊑` congruences are therefore
NOT restated here — they are tier-local by design.

---

## 2026-08-24-sv-1 — TRIAGE: SV does NOT want `real`, and the audit reword I accepted was never applied

Two items, one an answer owed outward and one a debt owed inward.

### The SoftFloat lane's question, answered: NO

`2026-08-22-softfloat-3` asked whether `docs/family-architecture.md`
§3.5.3's row — *"SystemVerilog | `real`, and the divider flagship"* — is a
need this tier actually has. **It is not.** Re-measured independently
here: `LeanModels/Sv/*.lean` contains **zero `Float`**, **zero
`shortreal`**, and every occurrence of `real` is the English word in prose
(`Tests.lean:15` "the **real** extractor envelopes", `:352` "real
vocabulary", `:441`/`:474` "real-schema", `:521` "byte-real"). The
SoftFloat lane's measurement is correct.

**The SV need is the divider, and nothing else.** That is not a hedge: the
flagship (`sv-charter.md` §6) is IEEE 754 *division*, which wants
SoftFloat's **spec layer** — `op_correct` as the correctly-rounded exact
rational result, decidable over `Rat`, no reals — and Berkeley HardFloat's
`divSqrtRecFN` as the RTL. Type-level `real`/`shortreal` in the SV
*language surface* is a different and much larger job: this tier's value
model is `Logic`/`LVec`, 4-state bit vectors, and `real` would be a new
scalar kind through the whole expression tier. **Nobody here asked for it,
and the estimate should not carry it.**

### And a debt this triage turned up in my own record

The 2026-08-23 quality audit flagged
`Examples/system-verilog/adder/proof.lean:275` — the guards claim to
*"reproduce the Xcelium-verified outcomes"* while `harness/sv/cases.json`
drives different vectors, so no simulator ever adjudicated them. I
recorded the disposition as **ACCEPTED, rewording** and then **never
applied it.** Measured today: the sentence is still in the tree at **10
sites** — `adder`, `counter`, `swap_nba`, `xsel` (both `proof.lean` and
`spec.lean`), plus `race_blk/spec.lean` and `toggle/spec.lean`.

Recording an acceptance is not the same as making the change, and the gap
survived two green landings because nothing gates prose against its own
audit disposition. **The reword is owed and now scheduled**, batched with
the next tier-`Sv` tenure since these are files inside the build glob;
docs-class cannot carry them.

### §5.0a declared-divergence register — this tier has two

Filed rather than left implicit, per the new register:

1. **The Xcelium 4-state operator table is unverified on any reachable
   host.** `docs/sv-design-m0.md` calls it *"normative — verified on
   Xcelium"*; Icarus reproduces the 10 harness cases, but the
   operator-level table has never been re-checked from here. Standing
   since `sv-charter.md` §9. **Gated**: no new claim may call it
   dual-simulator-verified without a re-run.
2. **10 guard sites claim Xcelium adjudication of stimuli no simulator
   ran** (above). **Debt**, with a scheduled remedy.

Both are provenance divergences rather than semantic ones — the model and
the simulator have not been shown to disagree; the claim of agreement is
what outruns the evidence.

---

## 2026-08-24-sv-2 — THE §5.0a REGISTER IS FILED: two provenance rows, four measured guards, and one row born with its retirement in flight

`docs/sv-declared-divergences.json` (DATA) + `harness/sv_divergence_probe.py`
(PROBE, named in every row). The shared CHECKER
`harness/divergence_register.py` has not landed yet; the data validates
against it when it does.

**Both rows are `KIND=provenance`, and the distinction is the whole reason
the field exists.** Neither says the model is wrong. Both say a CLAIM is
unsupported: **the model and the simulator have not been shown to disagree
— what outran the evidence is the claim of agreement.** Provenance retires
by **re-running**; semantic would retire by **remodelling**. Same register,
same gating, completely different work.

* **`sv-div-1`** — the Xcelium 4-state operator table, called *"normative
  — verified on Xcelium"* in `sv-design-m0.md` and never reproducible from
  this workspace. ORIGINATED here (no upstream to cite). Retires when a
  recorded xrun fixture lands under `harness/sv/` and is diffed against
  `Basic.lean`'s tables — the row tests the **fixture's presence**, so it
  cannot be closed by anyone deciding the tables look right. **Gated**: no
  claim in this tier may say dual-simulator-verified until it retires.
  Icarus reproduces the 10 harness **cases**; it has never adjudicated the
  operator **table**, and those are not the same claim.
* **`sv-div-2`** — 10 sites asserting the guards *"reproduce the
  Xcelium-verified outcomes"* while `cases.json` drives different vectors.
  Retires when the rewording lands; `still_divergent` counts surviving
  sites, so **the count reaching zero closes it — assertion cannot.**

**`sv-div-2` is the register's first row born with its retirement already
in flight**, and it is registered anyway rather than left as an in-flight
intention. The reason is in the row: this lane recorded the audit
disposition as *"ACCEPTED, rewording"* on 2026-08-23 **and then did not
apply it**, and the gap survived two green landings because nothing gates
prose against its own disposition. **Recording an acceptance is not making
the change. A row that ages is what makes that difference visible.**

**Run-not-read, honoured.** Every field the probe can back is measured, not
read: `sv-div-1` is still divergent because **no Xcelium fixture exists**
(0 found), `sv-div-2` because **10 claim sites survive**. Both refusal
directions were RUN, not admired — adding an 11th claim site makes
`sv_div_2_has_not_widened` report `11 (pinned <= 10)` and the probe exit 1.

**What "widened" means for a provenance row**, since the family's exemplar
is semantic: these rows do not describe a wrong answer, so widening is not
a semantic diff — it is **the unsupported claim SPREADING to more sites**.
Both `has_not_widened` guards are therefore claim-site counts pinned at
DECLARED (9 in `sv-design-m0.md`, 10 in `Examples/`).

**§9.0 line gains a third quantity**, per §5.0a's rule that a declared
divergence is neither coverage nor gap:

> **18 live / 21 envelopes · 11/11 constructs · 0/N semantics on `SvM` ·
> declared-divergences: 2**

---

## 2026-08-24-sv-3 — sv-div-2 RETIRES BY ITS OWN GUARD, and the `SvM` primitive layer is written

**THE REGISTER'S FIRST RETIREMENT, and the guard is what closed it.** All
**10** sites reworded from *"reproduces the Xcelium-verified outcomes"* to
*"consistent with the LRM rules the differential harness verified"*, each
now stating plainly that the guarded stimuli were **not themselves
simulated** and that `harness/sv/cases.json` drives different vectors.

`sv_div_2_still_divergent` then reported `sites: 0` and **FAILED** — which
is the guard working, not breaking: a row that is no longer divergent is a
**stale declaration**, and §5.0a calls a stale declaration *a false claim
about the tier that reads as diligence*. **The count closed the row; no
assertion could have.** Row and its two guards deleted in the same commit,
per §5.0a — *a guard whose row is gone guards nothing, and a row whose
guard is gone is unfalsifiable*. The row moves to `retired_rows` rather
than being dropped, because **a ledger that forgets its closed rows cannot
show that any row ever closes.**

Shared checker confirms: `sv  1 row(s), 2/2 guards held`.

**`LeanModels/Sv/Prim.lean` — the `SvM` primitive layer**, and the piece
§9.0's `0/N semantics on SvM` counts. `readSig`, `writeSig`, `pushNba`,
`commitNba`, `emit`, `finishSim`, `setRegion`, `advanceTime`, plus
`SvM.exec`. This is the whole per-language cost §4 prices — *the World
type, the error type, the primitive step functions and their laws* — and
the region ladder on top of it is supposed to be cheap **because** these
exist and are pinned.

**The load-bearing guard is `finish_preserves_out`.** This tier has
asserted in prose, repeatedly, that `$finish` belongs in `ρ` and not in
`Loud` because `SvWorld.out` carries the `PASS`/`FAIL` line that IS the
verdict for 97% of the corpus. That is a claim about **layer order** —
`ExceptT ρ` outside `StateT W` — and it is checkable rather than
believable:

    #guard ((okOf (SvM.exec (do emit "PASS"; finishSim .finish) w0)).map
              (fun w => w.out.flush)) == some ["PASS"]

If the transformers were nested the other way this reads `none`. That is
the same error the family document corrected by `rfl`, and the same one
that would have silently discarded the answer every conformance test
exists to produce. **Prose that has been repeated four times is exactly
the prose most worth turning into a guard.**

Ten more guards pin the rest: an undeclared read REFUSES rather than
defaulting; a nonblocking write is invisible before `commitNba` and
visible after; last-write-wins with the queue emptied; region and time
move.

**AND FIVE OF THE SIX ERRORS HAD ONE ROOT CAUSE I HAD A CHECK FOR AND DID
NOT RUN.** `Semantics.lean:394` already defines
`commitNba (st : SvState) (nba : NbaQueue) : SvState`. My monadic
`commitNba : SvM Unit` collided with it, which produced BOTH the
`already been declared` error at `:67` AND the three type mismatches at
`:127`/`:131`/`:133` — every use resolved to the pure two-argument
function instead of mine. **One rename to `applyNba` fixed four errors.**

I built the clash check after Landing A's `Res.pure_eq` red, ran it before
Landing B and it caught `Res.timeout_le` a tenure early — and then **did
not run it on `Prim.lean`.** It takes seconds and would have caught this
before the ticket. A check that exists and is not run is not a check; it
is a note about a check. (`emit` also flagged, and is NOT a clash:
`LeanModels/Python/Monadic/Prim.lean` is a different namespace — the same
true-negative shape as `Res.le_iff_flatLe`.)

**The sixth error is the declaration-slot family, seventh instance
campaign-wide.** I attached a `/-- … -/` **doc comment** to a `#guard`.
A doc comment must bind to a *declaration*, and `#guard` is a command, so
the parser reached `#guard` while still expecting `def`/`theorem`/… — the
long "expected declaration keyword" list. Fix: `/-! … -/`, a module doc,
which stands alone. Worth naming as a rule rather than an incident:
**`/-- -/` binds to the next declaration; `/-! -/` stands alone — and
`#guard`, `#eval`, `#print` are commands, not declarations.**

**I TRIED TO HOLD IT OUT OF THE BUILD, AND THE HOLD-OUT DOES NOT EXIST.**
The plan was: leave `Prim.lean` unimported from `LeanModels.lean`, elaborate
it via `--gates`, so a broken new file could not take the build red and
strand the retirement's evidence. **The build compiled it anyway** and went
red on it — errors at `Prim.lean:67,127,131,133,140` — and the gates never
ran, which is precisely the outcome the hold-out was meant to prevent.

**The rule I had in my head was wrong, and it was wrong the whole time.**
`lakefile.toml`'s `[[lean_lib]] name = "LeanModels"` carries no `globs`
key, and I read that as *"only the root module and whatever it imports."*
It is not: **the glob is by PATH, not by import graph — everything under
`LeanModels/` is a default target whether anything imports it or not.**
`docs/sv-step-wip.lean` escaped the build for a completely different
reason than I believed: it sat **outside `LeanModels/`**, and its being
unimported had nothing to do with it. The earlier landing worked by
accident of location, which is why the same trick failed the moment I
moved the file into the tier.

So there are exactly two real ways to keep a file out of a spine build —
**put it outside the globbed roots**, or **scope the ticket with
`--build-target`** — and the way to know which you have is to build before
ticketing rather than to reason about the lakefile.

**AND THE SECOND TENURE WENT RED ON SOMEBODY ELSE'S DATA — `build exit 0`,
gates RED.** `Prim.lean` was never the problem the second time; it built
clean. The failing gate was the SHARED checker
`harness/divergence_register.py`, and all **3** of its problems are in
`docs/es-declared-divergences.json`:

```
  missing top-level field 'probe'
  schema is 'declared-divergences-0.1', expected 'declared-divergences-1'
  row es-div-1 inherited_from is blank; use null to mean ORIGINATED here
  python  2 row(s), 4/4 guards held
  sv      1 row(s), 2/2 guards held
```

**The working hypothesis was that MY `retired_rows` key broke it. It did
not.** The checker has no unknown-key rejection — it validates
`REQUIRED_TOP` presence and row fields — so `retired_rows` passed
untouched, and the SV file reports `1 row(s), 2/2 guards held`. Worth
recording because the hypothesis was plausible and acting on it would have
meant **editing a shared instrument to accept a file that was already
fine**, while the actual non-conformance stayed hidden behind the change.
Diagnosing before acting is what kept the checker honest.

**The ES file is the pre-ruling shape**, filed as the DATA half before
§5.0a split DATA / CHECKER / PROBE. The checker is **correctly refusing a
file that predates the schema it now enforces**, so this lane proposed no
checker change: relaxing it would un-gate a real non-conformance. INBOUND
filed to `docs/backlog/es.md` as `2026-08-24-sv-4` with the three edits —
and deliberately NOT fixed here, because the `probe` field asserts *this
file measures that row*, and filing a provenance claim on another tier's
behalf is the defect registers exist to prevent.

**`divergence_register.py` dropped from SV's `--gates`, stated plainly.**
It was added voluntarily and is in no class floor (spine's floor is
`docs_check; diff_test; refusal_census`), so dropping it is not a fall
below the floor — but dropping a RED gate is exactly the move that must be
visible rather than quiet. SV keeps `harness/sv_divergence_probe.py`,
which passes, and puts the shared checker back the day the ES file
conforms.

**GATE RESTORED — the condition this lane stated has been met.** ES
normalized its register (master `133e87d`) and the shared checker now runs
clean here:

```
DECLARED-DIVERGENCE REGISTER — 3 tier file(s), 3 row(s), 6 guard(s) run
  es       1 row(s), 2/2 guards held
  python   1 row(s), 2/2 guards held
  sv       1 row(s), 2/2 guards held
divergence_register: OK — every row gated both ways, declared-divergences: 3
```

`harness/divergence_register.py` goes back into SV's `--gates` from the
next ticket. Verified by running it here rather than on report, because
the whole reason the gate was dropped was that a red had to be traced to
its actual owner — and the same standard applies to believing it is fixed.

**And the concern this lane FLAGGED rather than guessed is answered.** The
INBOUND noted that ES's guards were file-qualified where `python` and `sv`
use bare names, and said plainly that SV could not tell whether the
checker resolves a Lean-guard probe the way it resolves a Python one — and
that if it did not, that was a checker gap for pyc rather than something
to work around. It does: `es_div_1_still_divergent ok declared in
Examples/es/statements/guards.lean — **the BUILD is the run**`. Three
tiers, three probe shapes — a Python subprocess, a Lean `#guard`, and a
grep-based counter — under one checker. Guessing would have produced a
wrong bug report; flagging cost a sentence.

---

## 2026-08-24-sv-5 — `slotStep`: the Active/Inactive/NBA loop, and the clash check ran FIRST this time

`LeanModels/Sv/Slot.lean` — one IEEE 1800 §4.4 time slot against the
`SvM` primitives. `liftRes`, `runProcOnce`, `stepRegion`, `slotStep`.

**The loop is a recursion, not a sequence, and that is the whole content.**
Active → Inactive → NBA **iterating**: any region that did work sends
control back to Active, because Active is where that work lands, and the
slot closes only when all three are empty. A "one pass per region" model
reads almost the same and is wrong; §4.4's iteration rule is exactly what
it drops.

**`Res` is retained as a VIEW, as planned.** `stepSStmts` stays a pure
`Res`-valued function and `liftRes` carries its three outcomes across the
boundary — value to value, `timeout` to Core's `exhausted` (`Loud.timeout`
at the BASE, discarding a world a non-converging run cannot meaningfully
report), `unsupported` to a classified refusal carrying its clause. The
stepper is **lifted at the boundary, not rewritten into the monad**, which
is what lets the 23-lemma fuel-monotonicity ladder keep working untouched.

**Fuel stays semantic.** `Res.timeout` here means non-convergence — a
combinational loop, and now also a zero-delay loop that never lets the
slot close. Both are real properties of the design under test, so the loop
is fuel-bounded and exhaustion surfaces rather than being excluded by a
termination argument.

**Only three regions are implemented, and adding the rest changes no
type.** The reactive family and Preponed/Postponed are already
constructors of `Region` — carried from day one precisely so this inch
would not have to change the type. That decision pays here.

**THE CLASH CHECK RAN BEFORE THE FIRST LINE WAS WRITTEN.** Eleven candidate
names checked against the tree, all free. Then the four actually used were
re-checked after writing: `liftRes` flagged and is a **true negative** —
`LeanModels/Python/Monadic/Substrate.lean` has one in a different
namespace. Worth noting rather than dismissing: **two tiers independently
named the `Res`-to-monad bridge `liftRes`**, which is the same convergence
signal as three lanes choosing `line/col/endLine/endCol`.

This is the check whose *absence* cost a tenure on `Prim.lean`
(`commitNba`, five errors from one collision) and whose presence caught
`Res.timeout_le` a tenure early on `World.lean`. Running it first is now
the habit, not the lesson.

---

## 2026-08-24-sv-6 — `runSlots`: the adequacy lemma's missing left-hand side

`LeanModels/Sv/Drive.lean` — `setInputs`, `runSlots`, and six end-to-end
guards.

**Why this and not the transfer itself.** The transfer of the estate (162
trace-shaped declarations, 23 of them the fuel ladder) goes through

    cycleOf (runSlots …) = run …        on the cycle fragment

and **both sides have to exist before it can be stated.** The right-hand
side has existed since M0. `slotStep` runs one slot and mutates the world
— it produces no trace — so the left-hand side did not exist and there was
nothing for `cycleOf` to project. This file is that side. The third
ingredient, the oracle correspondence, landed at inch 2 as
`ScheduleOracle.toRegion` with `toRegion_choose := rfl`, for an unrelated
reason.

**The lemma is deliberately not attempted yet**, and the reason is now
sharper than "it is big": it carries **two** obligations at once — a
trace-type change AND a monad change, because the estate is stated over
`Res`-valued `run` while `runSlots` is in `SvM`. That second obligation is
this lane's own doing, from writing `slotStep` on the substrate first, and
it was the right trade for new code but it is a real cost and should be
named as one rather than discovered inside the proof.

**The Preponed sample is taken here and it is not decoration.**
`Slot.sampled` is read **before the stimulus lands**, which is what §4.4
means by Preponed: clocking blocks and concurrent assertions see values as
of before anything in the slot changed them. Nothing consumes it at this
inch. Taking it at the wrong moment would be invisible until the reactive
regions arrive and then very hard to find, so it is guarded now:
`sampled` reads `[1, 2]` where `final` reads `[2, 3]` — slot 1 samples
what slot 0 left.

**The adequacy PREREQUISITE is itself guarded**, which is the point of the
inch: `cycleOf` applied to a real `runSlots` trace yields the sequence of
slot `final` states — the exact shape the transfer will equate with `run`.
Not the lemma; the evidence that both its sides now exist and compose.

Fixture is a process-free world on purpose: `slotStep`'s ready sets are
empty, the loop closes immediately, and what is pinned is the DRIVER's
shape with no process semantics confounding it. Fuel exhaustion is guarded
too — zero fuel cannot close a slot, and the run is loud rather than
silently short.

Clash check ran first again: `runSlots`, `setInputs`, `traceOf` free;
`initWorld` taken by Python's namespace and avoided rather than shadowed.

---

## 2026-08-25-sv-1 — THE ADEQUACY LEMMA HAS A THIRD OBLIGATION, and finding it exposed a semantic gap the fixture concealed

Stating `cycleOf_runRegion` was the planned next step. **It cannot be
stated yet, and the reason is worth more than the lemma would have been.**

### The statement, and what blocks it

    theorem cycleOf_runRegion (d : Design) (h : d.isCycleFragment = true)
        (σ : ScheduleOracle) (fuel : Nat) (stim : List SvState) :
      -- LHS: (SvM.exec (runSlots σ.toRegion fuel stim) (??? d)).map cycleOf
      -- RHS: run d σ fuel stim

**Obligation 1 — trace type.** `RegionTrace` vs `List SvState`. **Solved**:
`cycleOf` exists and is guarded end-to-end (`2026-08-24-sv-6`).

**Obligation 2 — monad.** `SvM` vs `Res`. **Solved in shape**: `SvM.exec`
projects to `HaltWith … (Except Finish α × SvWorld)`; the equation needs a
projection on both sides, not new machinery.

**Obligation 3 — there is no `???`. `SvWorld` never mentions `Design`, and
no `Design → SvWorld` builder exists.** So the two sides cannot even be
said to be about the same design. `run` is `Design`-indexed; `runSlots`
operates on a world someone hand-built. **The lemma is not hard yet; it is
unstatable.**

### And obligation 3 is not glue — it is a semantic gap

`Design.processes : Array Process` is `alwaysFF clk body | alwaysPlain |
alwaysComb | assign | unsupported`. `SvWorld.procs : Array ProcState` is
`residual : List SStmt` plus a status. Turning the first into the second
means deciding what an `always` block IS as a residual — and

    | .done => { residual := [], status := .finished }

is what `runProcOnce` does today. **That is correct for `initial` and
WRONG for `always`.** An `always_ff @(posedge clk) body` is
`forever { @(posedge clk); body }`: it must RE-ARM after each completion.
As written it runs once and is permanently finished.

**`ProcState` cannot express re-arming** — it has a residual and a status,
and nothing that remembers what to restart from. Fixing it is a TYPE
change (an `arm : List SStmt` holding the body to reinstate, or a status
that carries it), which is exactly the kind of change the region-type
decision at inch 2 was designed to avoid needing — and this one was not
foreseen.

### Why nothing caught it

`runSlots`' guards used a **process-free world**, which I justified as
*"no process semantics confounding the driver's shape."* True as far as it
went, and the deeper reason is worse: **there is no way to load a process
at all**, so no fixture could have exercised re-arming. A fixture chosen
for isolation also concealed the gap it was isolating from.

The corpus census softens the impact and sharpens the priority: `initial`
is **98.8%** of the anchor corpus and `always_ff`/`always_comb` about
**1%** each, so the model is currently right for the dominant shape and
wrong for the rare one. That is the correct order to have built them in —
but it is not a reason to leave `always` silently wrong, because a process
that finishes when it should re-arm produces a SHORTER trace rather than
an error, and a short trace is the failure mode nobody notices.

### The next inch, priced from the real shape

1. **`ProcState` gains re-arming** — a type change, small, and the guard is
   an `always` process that runs twice.
2. **`elabDesign : Design → SvWorld`** — `alwaysFF clk body` becomes
   `[waitEvent clk .pos, body…]` re-armed; `alwaysComb` becomes a
   comb-sensitive process; `assign` likewise; `unsupported` stays loud.
3. **Then** `cycleOf_runRegion` is statable, and only then is it worth
   pricing the proof from a goal Lean will print.

Stated rather than attempted, which is the same discipline that worked for
the stepper's subsumption: build the definitions, name the obligation,
prove it against a real goal instead of an imagined one.

---

## 2026-08-25-sv-2 — RE-ARMING, WAKING, AND LOADING — and a FOURTH gap the same fixture concealed

Three definitions, built together because none is testable without the
others, and one of them was not on the plan.

**The fourth gap, found the same way as the third.** `regionQ` was only
ever **DRAINED**: `stepRegion` reads it and clears it, and **nothing in
the tier ever put an index into it.** So a process suspended on
`@(posedge clk)` could never become ready again, no scheduler run could
execute a second iteration of anything, and every trace would have been
silently short. `sawEdge`/`wakeEdges` are the missing half.

That is the **second** gap the process-free fixture concealed, after the
re-arm gap — and it is the same mechanism: a fixture chosen so that
process semantics could not confound the driver also removed the only
thing that would have exercised the scheduler's other half. Two findings
from one blind spot is a pattern, not a coincidence.

**What landed.**

* `ProcState.arm : Option (List SStmt)` — `none` runs once (`initial`),
  `some body` re-arms (`always`). `runProcOnce` now reinstates the body on
  completion instead of marking the process `.finished` forever.
* `sawEdge` / `wakeEdges` — edge detection and the `regionQ` fill.
  Edge detection follows **§9.4.2**: an `x`/`z` end IS an edge whenever
  the other end is a level (`0→x` and `x→1` are both posedges); only
  `x→z`, `z→x` and a value against itself are edgeless. *(This bullet
  originally claimed the opposite — see `2026-08-25-sv-3`, which is the
  correction and the reason this entry is not to be read as landed.)*
* `elabDesign : Design → Except String SvWorld` — the adequacy lemma's
  **third obligation**. `always_ff clk body` becomes
  `[waitEvent clk .pos, body]` **re-armed to itself**, which is the
  defunctionalized reading of `forever { @(posedge clk); body }`.

**`always_comb` and `assign` are REFUSED, not approximated**, and this is
the honest part. Their sensitivity is *"any signal the body reads
changed"*; `Trigger` offers `atTime`, `atEdge`, `onCond` — **none of which
expresses it**. The cycle model handles them by running to a fixpoint
(`combSettle`); the region model needs the same rule, and inventing a
wrong trigger to make them load would be worse than refusing. So designs
containing `always_comb` — including the `adder` gallery example — do not
load yet, while `always_ff` designs do. **The corpus census says that
order is right**: `initial` 98.8%, `always_*` about 1% each.

**The guard is the one that was specified**: two posedges over a REAL
loaded design, and the process is **not finished** afterwards — it
re-armed. Plus the driver produces one slot per stimulus entry over that
design, and `n` is actually assigned. Before `arm`, this process died
after its first body and every later slot silently did nothing.

**Not verified locally**: `check.sh --iterate` refused at memory pressure
**54%** against a 50% line (load was fine at 3.92). The batch was then
enqueued **blind** and went RED. What the blind enqueue cost is
`2026-08-25-sv-3`: the two compile errors were the cheap half, and behind
them sat two defects that would have shipped GREEN.

**And one merge casualty, restored.** `2026-08-25-sv-1` — the third
obligation entry — was **silently dropped** when the `sv-runslots` branch
merged: that branch was cut BEFORE `fb506dd`, so resolving the `sv.md`
conflict "to my side" took the OLDER file and reverted a later master
commit. `fb506dd` is an ancestor of `HEAD` and its 78 lines were absent
from the file. Restored byte-identically from `fb506dd`. **A branch cut
before a docs commit will silently revert it when the conflict resolves
in the branch's favour** — worth a check at every merge, not just this
one.

---

## 2026-08-25-sv-3 — THE RED WAS TWO NAMES; BEHIND IT WERE TWO DEFECTS THAT WOULD HAVE PASSED

Blind ticket `1787640148700009000-66640-sv`, tree `a3f3b78d41f3`, lock line
`[08:55:11] LOCK ACQUIRED as 'sv 66640'` → `[08:56:15] BUILD DID NOT
COMPLETE (exit 1)`. Claimed, diagnosed, fixed.

**The two root causes, against the real definitions.**

* `Load.lean:79:57` — `Unknown constant LeanModels.Sv.Expr.literal`. The
  constructor is **`Expr.lit (value : LVec)`** (`Ast.lean:60`). There is no
  `literal`.
* `Load.lean:105:32` — `Unknown identifier traceOf`. It exists, at
  `Drive.lean:91`, and it is **`private`** — so it is not in scope from
  another module. Not a typo: a visibility error, which is why a
  name-clash check could not see it.

The three `ffDesign` guard failures at 82-84 were cascade from the first.
**An error count is not a defect count** — two causes, five messages.

**And the errors were the cheap half.** The batch was enqueued without
elaborating, so nobody had traced it. Doing that by hand found two defects
that the fixed batch would have carried **green**:

### 1. Nothing was ever STARTED (the fifth gap, same blind spot as the fourth)

`stepRegion` reads **`regionQ`**. `ProcStatus.ready` is a *different*
notion of readiness and no rule connected them. `elabDesign` built its
processes `.ready` — and left `regionQ` at its default `fun _ => []`. So
every loaded design ran **nothing at all**: no process reached its
`@(posedge clk)`, and a process that never suspends can never be woken.
The previous inch added the queue's *fill* for waking and missed its fill
for *starting*, which is the same gap one step earlier.

Three edits, one gap: `elabDesign` schedules every process in Active at
time 0 (§4.4); `runProcOnce` re-enqueues a re-armed process; and
`stepRegion` **drains its queue before the pass instead of clearing it
after**, because clearing after discards exactly the re-entries the pass
itself created. The third was pre-existing and its docstring already
claimed the behaviour it did not have.

**Why the specified guard would not have caught it.** "The process is not
`.finished` afterwards" is TRUE of a process that never ran — it is still
`.ready`. The guard was vacuous in precisely the world it was written for.
It now also asserts the process is **waiting on its clock edge**, which a
never-run process is not, and `n == some 1`, which is the one that
actually fails when nothing executes.

### 2. The edge rule was three different rules at once

`sawEdge` was `o != some 1 && n == some 1` over `LVec.toNat?`. That says
`x→1` **is** a posedge and `0→x` is **not**. Its own docstring said
unknowns are never edges. The section comment above its guards said "x is
never an edge". And the fourth guard asserted `x→1 == true` — pinning the
code against both prose. Whichever you believed, one of the three was
wrong, and the guard block had been written to *pass* rather than to
*check*.

**IEEE 1800 §9.4.2 settles it**: posedge is `0→1, 0→x, 0→z, x→1, z→1`;
negedge the mirror. An `x`/`z` end IS an edge when the other end is a
level. The old rule had the "into a level" half and was missing the "out
of a level" half.

**And the tier already knew this.** `Sem2.isNegedge` (`Sem2.lean:579`)
states §9.4.2 exactly, for the async-reset phase. So the batch introduced
a *second, disagreeing* edge rule into the same tier — the shape the
standing rule calls a blocker, not a footnote. `edgeOn` now states the
clause once, over `Logic` bit 0, matching `isNegedge` case for case.

**The duplication is named, not fixed.** `Slot` sits below `Sem2` in the
import graph, and reaching `isNegedge` would mean importing the M1 cycle
model into the region tier — a worse dependency than a stated repetition.
Folding both onto one definition in `Basic` (where `Logic` lives) is the
next rung, and it replaces agreement-by-inspection with
agreement-by-construction.

**The lesson, priced.** The A17 iterate loop refused at 54% against a 50%
line, and the batch went out blind anyway. A blind enqueue buys a
*compile* verdict; it buys nothing about whether the definitions mean
anything. Both defects here were reachable by reading — no build required
— and both would have been certified green by the guards as written.


---

## 2026-08-25-sv-4 — A TENURE THAT REFUSED ITSELF: the progress log is inside the tree it stamps

`sv 80162` waited **8197s** for the lock, acquired it at `[11:49:11]`, and
refused in one second:

    TREE CHANGED SINCE ENQUEUE (28258373a128 → 95d827a4d4db)

**Nothing was edited.** The tracked tree was byte-identical to the commit
enqueued, `git status` was clean, and no lane had touched the clone.

**The stamp includes untracked files.** `worktree_tree` builds a temp index
with `git add -A` and writes a tree from it — so anything not gitignored is
part of the stamp. The tenure's own progress log lived at
`scratchpad/sv-red-refix.log` *inside the clone*, and while queued the
script appends a `queued Ns; head=…; owner=…` line every few seconds. It
had grown by **75 lines**. Those 75 lines were the "tree change".

Measured, three ways:

    tracked only            566cae7e…   == git rev-parse HEAD^{tree}
    tracked + small log     28258373…   == the enqueue stamp
    tracked + grown log     a5ed611e…   == the refusal's "now"

**The failure is self-inflicted by construction and scales with the wait.**
A short queue hides it — the predecessor's `scratchpad/sv-rearm.log` sat in
the same place and its lock came 11 seconds after enqueue, so the log had
not grown yet. The longer a tenure waits, the more its own logging diverges
the tree from the one it is about to verify. **A machine under load makes
this MORE likely, which is exactly backwards**: the tenures that waited
longest are the ones that lose their turn, after paying the full wait.

**Fix taken here**: the log moved OUTSIDE the clone
(`../sv-logs/`), leaving the clone pristine — its stamp now equals
`HEAD^{tree}` exactly, so it cannot drift for any wait length.

**Fix worth taking fleet-wide** (arch's call, not this lane's): `scratchpad/`
is not in `.gitignore`, and lanes are writing tenure logs into it inside
their clones. Either ignore it, or have `triad.sh` refuse to write its own
log beneath `$CLONE`. The protocol's own artifact should not be able to
invalidate the protocol's own ticket.

**And a second refusal behind the first.** The re-enqueue reported
`BASE STALE: 21 commit(s) behind`. Rebasing while queued would have changed
the stamp and self-refused a third time, so the order is forced and worth
stating: **cancel, rebase, re-enqueue** — never rebase a ticket that is
already in the queue.


---

## 2026-08-25-sv-5 — THE ADEQUACY LEMMA IS STATABLE, AND STATING IT FOUND TWO MORE OBSTRUCTIONS

All three obligations were discharged — `cycleOf` exists (inch 4),
`SvM.exec` projects (inch 4), `elabDesign` loads a `Design` (inch 4a) — so
the lemma should have been a matter of writing it down. It was not.

### Obstruction 1: the two models do not take the same stimulus

**The M0 clock is IMPLICIT.** `Semantics.lean` says it outright: *every
`cycleStep` is one posedge of the (single) clock*. A cycle-model stimulus
drives the DATA inputs and never mentions a clock, so `run d σ fuel stim`
returns exactly `stim.length` states.

**The region model has no implicit anything.** A process suspended on
`@(posedge clk)` wakes only when `wakeEdges` sees `clk` go 0 → 1, and
driving a real edge costs **two** stimulus entries. `runSlots` over the
same list produces `stim.length` slots with **no posedge among them**.

So `run … = cycleOf (runSlots …)` was never merely unproved — the left
side counts CYCLES and the right counts TIME SLOTS. Two definitions close
it: `clockExpand` (2 slots per cycle, low then high) and `posedgeSlots`
(keep the slot the edge ran in; a trailing unpaired slot is a cycle whose
clock never rose and is dropped).

### Obstruction 2: found by computing, not by reading

The expansion **introduces a signal the cycle model never has**. `clk` is
driven 0/1 on the region side and stays `x` on the cycle side forever,
because nothing in the cycle model ever assigns the clock it is
implicitly stepping. **A whole-state equality between the two runs is
therefore false for a reason that has nothing to do with adequacy.**

The comparison must go through an OBSERVATION, and `d.outputNames` is the
honest one — it is what a cycle-level observer can see, and it is already
the shape `divResult`/`sampleAtFirst` observe through. This is PINNED, not
described: three guards assert the two models agree on `n` and *disagree*
on `clk`, so the reason for the projection cannot be quietly forgotten.

### What is guarded, and what is only stated

**Guarded**: both translations, and — the load-bearing one — that the two
models AGREE on a real `always_ff` design through the expansion and the
decimation, each side also pinned separately so a failure says which model
moved. That is executable evidence the statement is plausible, and it is
what catches a wrong expansion immediately.

**Stated, not proved**: `CycleAdequacy`, quantified over `∀ σ` with
`σ.toRegion` on the region side. Its loadability hypothesis is
`elabDesign d = .ok w` and NOT `d.isCycleFragment`, deliberately: the
fragment predicate admits `always_comb` and `assign`, which `elabDesign`
refuses, so stating it over the fragment would make the lemma false for a
reason already known and named.

### The proof, priced

Induction on `stim` with the world and state generalized, over a per-cycle
correspondence lemma that needs four pieces:

1. the LOW slot is observably inert — no process is ready, so nothing runs;
2. `wakeEdges` at the HIGH slot wakes exactly the `alwaysFF` processes,
   which is `sawEdge`'s §9.4.2 rule meeting `Trigger.atEdge`;
3. the Active pass runs each woken body exactly once, and its NBA commit
   agrees with `edgePass`'s commit;
4. the re-arm's SECOND Active pass is observably inert — it only walks to
   `waitEvent` and suspends.

Piece 4 is the one the `arm` field created and the one no guard pins as a
lemma today: `runProcOnce`'s re-arm is currently evidence-by-`#guard`, and
the proof needs it as a statement. Piece 3 is the real work; 1 and 2 are
bookkeeping over definitions that now exist.

**Not attempted here**, for the reason this lane has applied three times: a
proof written against an imagined goal is worth less than a statement
written against a real one.

