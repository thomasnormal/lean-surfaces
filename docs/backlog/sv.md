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
