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
