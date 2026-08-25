/-
sunfish pin file: the pass-4 capstone — `Searcher().bound()` END TO
END on the shipped file (the 23-pair CPython battery; node-count
equality is the lockstep signal) — and the trace-clock pins (the
2048-node frontier underrun, the armed deadline pair).

Part of the pass-7 SPEC-POLE SPLIT (docs/backlog.md §Pass 7): the
program and shared probe defs come from `pins_common.lean` — after an
envelope re-extraction, edit THAT file (the JSON trap note there); this
file rebuilds through the import.

THE BATTERY IS SHARDED (2026-08-25). This file keeps the prose and the
map; the probes live in five leaves that elaborate in PARALLEL, because
a single module elaborates serially and this pair plus `pins_clock` was
~85% of every full spine build. NO probe was dropped, NO fuel changed,
and every expected value is byte-identical — a topology change must not
move a certificate.

  `pins_bound_h`         the opening board `posH 0`, depths 1-3   (8)
  `pins_bound_mid`       the midgame board `posMid`               (6)
                         -- itself split by DEPTH after the profile
                            measured it at 74% of this family:
                            `_mid_d1` (2) `_mid_d2` (2) `_mid_d3` (2)
  `pins_bound_tac`       tactical `posTac` + quiet-pawn `posPend` (5)
  `pins_bound_end`       rook endgame `posEnd`                    (4)
  `pins_bound_searcher`  the trace-clock frontier                 (3)

The boundary is by POSITION so a red names its board.
-/
import Examples.python.sunfish.pins_bound_h
import Examples.python.sunfish.pins_bound_mid
import Examples.python.sunfish.pins_bound_tac
import Examples.python.sunfish.pins_bound_end
import Examples.python.sunfish.pins_bound_searcher

/-! ### THE PASS-4 CAPSTONE: `Searcher().bound()` runs END TO END on
the shipped file

Every probe instantiates a fresh `Searcher()` — the hand-built call
below, CPython's own driver shape: `__init__`'s two tuple-ATTRIBUTE
unpacks bind the empty tables, the empty history set, `nodes = 0` and
`deadline = 1 << 63` (the pass-5 shift tier; post-#158 there is NO
None test — `time.time()` evaluates at every 2048th node, so every
row below stays under 2048 nodes and the first crossing is pinned as
the LOUD refusal at the end of this battery) — in the module's REAL
`initWorld`, calls the shipped `Searcher.bound` through `callIn` with
`root` filled from its literal default, and reads back the RETURNED
BOUND and `self.nodes` from the instance: the pair CPython answers.

NODE-COUNT EQUALITY IS THE LOCKSTEP SIGNAL: `self.nodes += 1` runs
once per entry, so one extra or missing node anywhere in the tree — a
mis-ordered move list, a wrong futility/beta cutoff, a table probe
that hit where CPython missed, a correction scan that ran where
CPython's didn't — breaks the pair. Live in these runs: the tp_score
probe under the dict-key doctrine (`(pos, depth)` tuple keys carrying
the Position value), the history-set membership, the nested `moves()`
generator with recursion through the captured `self`, the killer
prologue (`killer = self.tp_move.get(pos)`, read before the null probe
and yielded out of order under its own ceiling), the null-move gate
with the SCORE CAP (`score = min(cap, -self.bound(…))` where
`cap := pos.score + EVAL_ROUGHNESS`, a WALRUS in general expression
position — §L14's tier item 3), the QS ordering line with the WALRUS
FILTER (`if (v := pos.value(m)) >= QS or depth` — filter-before-sort;
the sub-threshold tail is never sorted) delegated through a general
`yield from sorted(…)`, the CELLED capture `guard` (written below the
`def`, read at the call — §L14's cell), the fold with its five scoring
branches and the SETTLED-CAP BREAK (`if cap < gamma: best = max(best,
cap); break`), the `not live` correction gate carrying the mate
DISTANCE, the attribute `+=`, and the table store.

Every expected pair below is CPython's own answer, re-derived against
engine master `e670434` and never reused — **pass 8 moved fourteen of
the 23 pairs**. Where they moved and where they did not is the
measurement:

* **twelve rows kept their VALUE and lost nodes** — #236's
  settled-cap break leaves the fold earlier on a sorted stream, so the
  same bound is reached from fewer entries (`posH 40 3`: 208 → 197
  nodes at the same 39; `posEnd 60 3`: 27 → 13 at the same 137).
* **the two TACTICAL rows changed value outright**, and they are the
  finding: pass 7's `posTac` answered exactly `MATE_LOWER = 47923` at
  both depths — the king-capture sentinel path — and engine master
  answers `277` / `417`. The futility cap now settles the position
  before the mate line is searched at all, so the sentinel discipline
  is simply not exercised by this board any more. Recorded rather
  than repaired: it is CPython's answer, checked directly.
* the endgame rows still walk the correction (depth 3 at gamma 0
  answers the repetition/stalemate-corrected 0). -/
