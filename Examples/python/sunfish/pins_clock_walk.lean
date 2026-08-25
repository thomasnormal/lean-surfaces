/-
sunfish pin shard: the DEEP STEPPING walk — `search()` to depth 4 under
a seeded trace. THE HOT ONE, and it is ONE guard.

SHARD of the `pins_clock` battery (2026-08-25 topology change): the prose
and the shard map are in `pins_clock.lean`. Every `#guard` moved VERBATIM;
`searcherWT`/`boundProbeT` moved to `pins_common.lean` unchanged.
-/
import LeanModels
import Examples.python.sunfish.pins_common

namespace Examples.python.sunfish.pins_clock_walk

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins

/-! ### DEEPER STEPPING THROUGH THE WALL (the pass-7 close of the
pass-5 frontier): `search()` stepped to depth 4 under a SEEDED trace

The pass-5 capstone stopped at three yields — under engine master the
empty trace refuses at the end of depth 1 (`if time.time() >
self.soft: return`), and the 2048-node `bound()` wall stands between
depth 3 and depth 4 behind it. THE TRACE CLOCK opens both: with FOUR
seeded readings the stepping runs the depth-1/2/3 brackets to
convergence and crosses node 2048 inside step 13 (depth 4's first
yield, both walls consulted against `1 << 63` and both passed), and
every `(depth, gamma, score, move)` tuple AND cumulative `self.nodes`
below is CPython's own answer
(the counting-clock oracle: integer reading 0, calls counted).

**PASS 8 — the consumption pattern changed, and it is now the pin's
real content.** Engine master ends every depth iteration with
`if time.time() > self.soft: return`, so the driver consults the wall
once per COMPLETED DEPTH as well as at the 2048-node bound() frontier.
Under a four-reading trace the walk consumes them at exactly four
places, all measured:

| between | why | trace after |
|---|---|---|
| steps 3 → 4 | depth 1 converged | 3 left |
| steps 7 → 8 | depth 2 converged | 2 left |
| step 13 | depth 3 converged **and** node 2048 crossed inside `bound` | 0 left |

So the empty trace no longer reaches step 12 at all — its refusal is at
the END OF DEPTH 1, four yields earlier, and is pinned at that point by
`pins_search.lean` (45 nodes in, not 2048). What this file pins is the
seeded direction: the whole depth-1/2/3 bracket plus depth 4's first
yield, every tuple and cumulative `self.nodes` CPython-exact, and the
trace drawn down to empty exactly on schedule. Depth 3 now takes FIVE
probes to converge where pass 7 needed four, so the walk is 13 steps
rather than 12. -/

/-- `Searcher().search([posH 0])` created under a seeded trace. -/
private def searchGenT (tr : ClockTrace) : Option (World × Addr × Addr) :=
  match searcherWT tr with
  | some (w, a) =>
    let histA := w.heap.size
    let w2 := { w with heap := w.heap.push (.list #[posH 0]) }
    (match callIn sunfish 4096 w2 "Searcher.search" #[.ref a, .ref histA] with
     | .ok w' (.ref g) => some (w', a, g)
     | _ => Option.none)
  | Option.none => Option.none

/-- Step the search generator `n` times: per step, the yielded
`(depth, gamma, score, move)` and `self.nodes` after the step — AND the
final world (the trace-consumption probe rides the same walk: one pass,
never a from-scratch re-walk per pin). -/
private def searchStepsW (sa g : Addr) :
    Nat → World →
      Option (List ((Int × Int × Int × Option (Int × Int × String)) × Int) × World)
  | 0, w => some ([], w)
  | n + 1, w =>
    match stepIter sunfish 4000000 w g with
    | .ok w' (some (.tuple #[.int d, .int gm, .int sc, mv])) =>
      (match Heap.get? w'.heap sa with
       | some (.instance _ attrs) =>
         (match Env.lookup attrs.toList "nodes" with
          | some (.int nn) =>
            (match (match mv with
                    | .ntuple _ _ #[.int i, .int j, .str p] => some (some (i, j, p))
                    | .none => some Option.none
                    | _ => Option.none) with
             | some mvv =>
               (searchStepsW sa g n w').map fun (rows, wF) =>
                 (((d, gm, sc, mvv), nn) :: rows, wF)
             | Option.none => Option.none)
          | _ => Option.none)
       | _ => Option.none)
    | _ => Option.none

-- ONE PASS pins everything: steps 1–12 (the depth-1/2/3 brackets to
-- convergence — tuples and nodes CPython-exact) draw the trace down to
-- TWO readings (`w12.clock == [0, 0]`: one spent at the end of depth 1,
-- one at the end of depth 2 — the soft-limit line, not the node wall),
-- and step 13 — depth 4's first yield — spends BOTH remaining readings:
-- depth 3's own soft-limit check and the 2048-node crossing inside
-- `bound`. It continues to CPython's (4, 33, 32, g8f6) with the trace
-- EMPTY. The consumption schedule is the positive proof of where the
-- consultations are; the loud direction is `pins_search.lean`'s
-- empty-trace refusal at the end of depth 1.
#guard (match searchGenT [0, 0, 0, 0] with
        | some (w, sa, g) =>
          (match searchStepsW sa g 12 w with
           | some (rows, w12) =>
             rows ==
               [((1, 0, 0, some (84, 64, "")), 2),
                ((1, 34645, 46, some (84, 64, "")), 3),
                ((1, 23, 37, some (97, 76, "")), 45),
                ((2, 42, 41, some (97, 76, "")), 91),
                ((2, -34624, -9, some (97, 76, "")), 93),
                ((2, 16, 13, some (97, 76, "")), 331),
                ((2, 2, 4, some (97, 76, "")), 344),
                ((3, 9, 11, some (97, 76, "")), 463),
                ((3, 34651, 326, some (97, 76, "")), 464),
                ((3, 169, 46, some (97, 76, "")), 506),
                ((3, 29, 29, some (97, 76, "")), 696),
                ((3, 38, 36, some (97, 76, "")), 795)]
               && w12.clock == [0, 0]
               && (match searchStepsW sa g 1 w12 with
                   | some (rows13, w13) =>
                     rows13 == [((4, 33, 32, some (97, 76, "")), 2053)]
                       && w13.clock.isEmpty
                   | Option.none => false)
           | Option.none => false)
        | Option.none => false)

end Examples.python.sunfish.pins_clock_walk
