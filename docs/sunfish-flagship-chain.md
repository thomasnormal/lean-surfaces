# The chain to `bound_refines_fuelModel`

**The flagship of the sunfish R-track, and the distance to it, stated as rungs
rather than approached implicitly.** Per Thomas's scale recalibration
(2026-08-23): milestones are waypoints, the goal is completing the project. This
document fixes the denominator so that "how far" has an answer that is a number
and not a mood.

**§9.0 number for this lane: `chain rungs closed / total`.** Today: **5 / 9**, and the chain is now WHOLLY INTERNAL.

---

## §1 THE THEOREM

`bound_refines_fuelModel` says the shipped `Searcher.bound` keeps the promise its
own docstring makes. **It is now STATED IN LEAN** —
`Examples/python/sunfish/flagship.lean` — where for the whole campaign before
2026-08-24 it existed only as prose in `docs/backlog-archive.md` and in three
successive "and then it assembles" ladders.

Rung 1 was listed first because a goal theorem that has never been typed is a
goal nobody can typecheck against: every WAITING trigger aimed at it is
unexecutable, and every claim to be serving it is unfalsifiable. Typing it
converts all three into machine-checkable things.

**And it does more than type: it ASSEMBLES.** The strong induction is discharged
in that file, so the flagship reduces to exactly two named obligations and no
proof shape — `BoundRefinesW V 0` (rung 8, base-case lane) and `RecursionStepW V`
(rung 7, this lane). Neither is discharged there, so the theorem has genuine
hypotheses; when they land it closes by application and nothing about its shape
is then in question.

**The model choice is already ruled** (archive, §L17 successor): the theorem is
stated against **the docstring's `s*`**, in which the per-move futility bound and
the reduction bound are DEFINITIONAL, because the docstring defines `s*` to
include "null moves, QS, futility and the reductions". `formal/`'s `CapInBand`
carries the unreduced-negamax gap as a recorded axiom. The split is clean:
*lean-surfaces proves the code keeps its own documented promise; `formal/` proves
the promise is worth having.*

**The scope is ruled REAL-PLAY** (2026-08-23): the theorem covers the table
eviction paths. The cheap version — preconditioned on the tables never exceeding
`TABLE_SIZE` — is rejected, because the eviction policy was a bug fix bought with
production losses (the comment above sunfish.py:511 records three queen/piece
giveaways in 145 games from FIFO aging), and a flagship refinement that excludes
it excludes the part that was hardest to get right.

## §2 THE SPINE

Four objects, in dependency order. All four exist on the trunk; the flagship is
their composition.

* `RefinesAt V d w sa ts gamma pos` — the per-node conclusion.
* `BoundRefinesW V d` — `RefinesAt` at every well-formed state. **The `W` matters:
  plain `BoundRefines` is FALSE** (`not_boundRefines` refutes it at
  `pos := .int 5`, where the shipped `bound()` reaches `pos.score` and refuses),
  which made `RecursionStep` vacuously true. The repaired proposition is the one
  the chain uses.
* `RecursionStepW V` — strong induction: for `d ≥ 1`, `BoundRefinesW` at every
  `0 ≤ e < d` gives `BoundRefinesW V d`. **Strong, not predecessor-step**, and
  that was decided at plan time rather than at proof time: `bound()` recurses at
  `depth - 1`, at `depth - 3` under the intrinsic reduction, and at `depth - 7`
  for the deep-null probe.
* `bound_refines_fuelModel` — the induction discharged against the base case.

## §3 THE RUNGS

Status vocabulary: **MECHANICAL** = no unknown, only work. **BLOCKED** = waits on
a named artifact owned elsewhere. **OPEN** = this lane owns it and it has an
unsolved question in it.

| # | rung | owner | status |
|---|------|-------|--------|
| 1 | State `bound_refines_fuelModel` in Lean, and discharge its induction | R-track | **CLOSED** |
| 2 | R2 ordering line, monadic — generator judgment layer | R-track | **CLOSED** |
| 3 | R2 ordering line, monadic — the caller's chain induction | R-track | **CLOSED** |
| 4 | R3 fold, spec side (`FoldInv` over `RoundOK`) | R-track | **CLOSED** |
| 5 | R3 fold, interpreter half on the monadic fold | R-track | OPEN (round law landed) |
| 6 | The ~57 interpreter-facing statement gates of `bound()`, re-proved monadically | R-track | OPEN |
| 7 | `RecursionStepW V` assembled | R-track | MECHANICAL after 3,5,6 |
| 8 | Base case `BoundRefinesW V 0` | base-case lane | BLOCKED (their ledger) |
| 9 | Three tier surfaces for real-play scope | pyc lane | **CLOSED (with scope)** |

**Closed: 5 of 9** — rung 9 (pyc inch 3, `cf13932`: `bound()`'s unsupported
census is ZERO, all three flagship-serving surfaces landed, scoped by the
`scope_against_real_play` register row), rung 1 (`flagship.lean`: the theorem typed and its induction
discharged), rung 2 (`GenEmitsM.forGenRound`), rung 3 (`forGenChain`: the
caller's induction discharged once, over `ForGenRunM`) and rung 4
(`FoldInv`/`.step`/`.nil`/`.run` in `monadic_fold.lean`).

**Rung 5 is the live one, and it has its floor.** `forGen_step` / `forGen_done`
are the fold's interpreter half at its lowest altitude — one round and
exhaustion. They are stated over `forGenAt`, NOT the `execGenAt` frame arm that
rungs 2–3 use, because `bound()` is not itself a generator: its
`for val, move in moves():` is a plain loop through `execOpen`. Same recipe,
different function. A lane that proved the frame arm and assumed the loop arm
came with it would have a gap exactly where the fold lives.

Rung 1 cost one scratch elaboration. That is worth recording next to the number:
the rung listed first, blocking the most triggers, and carrying the campaign's
name, was the cheapest one on the board — it had simply never been anyone's
explicit task.

## §4 RUNG 6 IS THE BULK, AND ITS NUMBER IS MEASURED

The re-founding makes every interpreter-facing trunk theorem class-4: re-proved,
not transported. The raw counts are frightening and wrong — `bound_depth.lean`
holds 221 theorems and 63 statement-slice definitions. **The corrected count is
what matters**: `docs/python-refounding-plan.md` §2.6 counts only
INTERPRETER-FACING statements and gets **57** for `bound_depth`, 82 for
`genmoves_ray`, 61 for `move_gate` — 200 across the three, not 558.

So rung 6 is ~57 statements. **But they are not ~57 independent proofs, and that
is now measured rather than hoped.** They are ~57 INSTANTIATIONS of a handful of
ARM lemmas — one per shape a generator-body statement can take (`.branch`,
`.delegate`, the loop arms) — each supplying a `genPlan` equation, discharged by
`rfl` on a slice, and whatever sub-runs its own statement makes. The arms are
shared infrastructure; only the premises are per-statement.

The price measurement that established this: `genSilent_branch'` and
`genSilent_delegateNext` (§9 of `monadic_gen.lean`), both proved first shot in a
scratch iteration. `delegateNext` is the high-frequency one — most of `moves()`
is assignments and calls, not control flow — so the arm that covers the most
statements is already in hand.

It also exposed a defect in this lane's own earlier work: §5's `genSilent_branch`
hard-codes `Stmt.ifStmt`, which is the right shape for proving an arm EXISTS and
the wrong shape for USING it, since a real slice presents as an opaque `Stmt`
with a computed `genPlan`. The trunk's lemma takes `s` plus a plan premise for
exactly that reason. **Re-founding copied the proof and not the interface**, and
that is a failure mode worth naming: a ported lemma can be true, green, and
unusable.

**The `twinAgrees` fork, and why it is NOT taken.** A whole-interpreter adequacy
theorem would transport all 57 at near-zero marginal cost. The refounding plan
prices it: transport pays only if one file carries more than ~100 theorems of
mostly-mechanical value-claims, and **no file clears that on the corrected
count**. `twinAgrees` is a whole-interpreter induction — the genuinely hard
artifact — and the plan's standing instruction is *do not start it
speculatively*. This lane follows that: rung 6 is re-proof, and `twinAgrees` gets
reconsidered only if the first dozen statements resist.

## §5 THE EXTERNAL DEPENDENCY — DISCHARGED

Real-play scope made `bound()`'s two eviction sites reachable, and both were
`Unsupported` **at ingestion** — not merely unproven but unrepresentable. Three
surfaces were owed: `del d[k]`, `iter(d)` + `next(...)`, and
`next(<genexp over dict keys, with filter>)`.

**All three landed** with the pyc lane's inch 3 (`cf13932`), and `bound()`'s
unsupported census is now **zero**. The scope under which that holds travels in
the register's `scope_against_real_play` row rather than being restated here; the
one divergence behind it is a declared debt with a live two-sided probe, not a
silent exclusion.

**So the chain has no external dependency left.** Everything between the typed
flagship and its discharge is rungs 5 and 6 (this lane's, entangled) and rung 8
(the base-case lane's `BoundRefinesW V 0`). That is worth stating plainly because
it changes what "blocked" can mean for this lane: nothing is waiting on anyone
outside the two proof lanes, so every remaining rung is work rather than
sequencing.

## §6 WHAT THIS DOCUMENT IS NOT

It is not a schedule. No rung here carries a date, because this lane has twice
measured that the queue, not the proving, sets the clock. It is a denominator and
a dependency order, so that "closed / total" is checkable by anyone and the
flagship stops being a direction and becomes a distance.
