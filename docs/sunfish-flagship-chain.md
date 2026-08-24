# The chain to `bound_refines_fuelModel`

**The flagship of the sunfish R-track, and the distance to it, stated as rungs
rather than approached implicitly.** Per Thomas's scale recalibration
(2026-08-23): milestones are waypoints, the goal is completing the project. This
document fixes the denominator so that "how far" has an answer that is a number
and not a mood.

**§9.0 number for this lane: `chain rungs closed / total`.** Today: **3 / 9.**

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
| 3 | R2 ordering line, monadic — the caller's chain induction | R-track | MECHANICAL |
| 4 | R3 fold, spec side (`FoldInv` over `RoundOK`) | R-track | **CLOSED** |
| 5 | R3 fold, interpreter half on the monadic fold | R-track | OPEN |
| 6 | The ~57 interpreter-facing statement gates of `bound()`, re-proved monadically | R-track | OPEN |
| 7 | `RecursionStepW V` assembled | R-track | MECHANICAL after 3,5,6 |
| 8 | Base case `BoundRefinesW V 0` | base-case lane | BLOCKED (their ledger) |
| 9 | Three tier surfaces for real-play scope | pyc lane | BLOCKED (sequenced after 3c-i-c) |

**Closed: 3 of 9** — rung 1 (`flagship.lean`: the theorem typed and its induction
discharged), rung 2 (`GenEmitsM.forGenRound`, seventeen theorems in
`monadic_gen.lean`) and rung 4 (`FoldInv`/`.step`/`.nil`/`.run` in
`monadic_fold.lean`).

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

So rung 6 is ~57 statements, each a `py_simp`-shaped gate re-aimed at the monadic
interpreter. That is large but bounded, and the per-statement cost is now known
rather than guessed: the `toRun` seam (`Substrate.lean` §4) plus the
computed-shape discipline closes these in a scratch loop without a build tenure.

**The `twinAgrees` fork, and why it is NOT taken.** A whole-interpreter adequacy
theorem would transport all 57 at near-zero marginal cost. The refounding plan
prices it: transport pays only if one file carries more than ~100 theorems of
mostly-mechanical value-claims, and **no file clears that on the corrected
count**. `twinAgrees` is a whole-interpreter induction — the genuinely hard
artifact — and the plan's standing instruction is *do not start it
speculatively*. This lane follows that: rung 6 is re-proof, and `twinAgrees` gets
reconsidered only if the first dozen statements resist.

## §5 THE EXTERNAL DEPENDENCY, NAMED

Real-play scope makes `bound()`'s two eviction sites reachable, and both are
`Unsupported` **at ingestion** — not merely unproven but unrepresentable. Three
surfaces, measured from the AST rather than recalled:

1. `del d[k]` — `Delete` with a `Subscript` target on a dict. Both sites.
2. `next(<genexp over dict keys, with filter>)` — sunfish.py:511.
3. `iter(d)` then `next(...)` — sunfish.py:541.

(2) and (3) are the live-dict-iteration class. Everything else in `bound()` is
representable today: it runs on both interpreters, which the depth-1 ledger rows
demonstrate.

## §6 WHAT THIS DOCUMENT IS NOT

It is not a schedule. No rung here carries a date, because this lane has twice
measured that the queue, not the proving, sets the clock. It is a denominator and
a dependency order, so that "closed / total" is checkable by anyone and the
flagship stops being a direction and becomes a distance.
