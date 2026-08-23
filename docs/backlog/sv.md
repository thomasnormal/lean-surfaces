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

## INBOUND FROM THE SOFTFLOAT LANE — `2026-08-22-softfloat-3` (SV lane's to triage)

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

## INBOUND FROM THE FAMILY-ARCHITECTURE LANE — `2026-08-23-architecture-33` (SV lane's to renumber or close)

*Filed as its own immediate commit (§9.5a's tightening). Named rather than
edited: a dated measurement in another lane's document is the lane's own record
of a moment, and correcting it in passing would turn it into a record of mine.*

### `docs/sv-charter.md:138`'s VENV MEASUREMENT WILL QUIETLY STOP BEING TRUE

The line prices the absent frontend: *"a clean `python3.12 -m venv` +
`pip install pyslang` yields **pyslang 11.0.0** — inside the extractor's
declared 11.x range."* **That was a measurement of an unpinned resolver**, so it
is a statement about **what PyPI served that day**, not about the command. At
pyslang's next release the same command yields a different version and the
sentence is false — silently, with nothing failing.

This is the same input that made the round-trip gate an armed bomb once it went
unconditional (`docs/family-architecture.md` §5.4b; `582529d`, `b499afa`): all
21 envelopes stamp the **point** version, and the interim pin is temporary by
design.

**Asked for, and it is small:** either **stamp the line** — *"11.0.0, resolved
`<date>`, unpinned"* — so a stale number is **readable** rather than wrong, or
carry it forward with the durable family stamp when Landing A lands. **The fix
is the stamp, not the refresh** (`docs/backlog/architecture.md`
`2026-08-23-architecture-24`), and §0's *"every extractor claim was made through
that venv"* inherits whatever this line says.

*Renumber into your sequence or close it — the call is yours.*
