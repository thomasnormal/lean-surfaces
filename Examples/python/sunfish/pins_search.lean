/-
sunfish pin file: the pass-5 capstone — `search()` STEPPED on the
shipped file (the full depth-1 MTD-bi bracket to convergence plus the
depth-2 rollover; tuples AND cumulative `self.nodes` CPython-exact) and
the prologue's world effects after one step.

Part of the pass-7 SPEC-POLE SPLIT (docs/backlog.md §Pass 7): the
program and shared probe defs come from `pins_common.lean` — after an
envelope re-extraction, edit THAT file (the JSON trap note there); this
file rebuilds through the import.
-/
import LeanModels
import Examples.python.sunfish.pins_common

namespace Examples.python.sunfish.pins_search

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins

/-! ### THE PASS-5 CAPSTONE: `search()` STEPPED — the MTD-bi driver
runs on the shipped file

`Searcher().search([posH])` is the real driver surface: a GENERATOR
METHOD (H4 allocates it, running NO code — the prologue fires on the
first `next`, as CPython). Stepping it exercises every pass-5
construct in the shipped positions: the prologue's
`self.tp_score.clear()` (the dict mutator), the chained
`pos = self.root = history[-1]` (split at ingestion), the LIVE-VIEW
store `pst["K"] = K_MID if "Q" in pos.board and "q" in pos.board else
K_END` (both queens on the opening board → K_MID), `set(history)`
through the boundary-free heap, then the iterative-deepening `for
depth in range(1, 1000)` frame, the MTD-bi `while lower < upper -
EVAL_ROUGHNESS` frame, root-probe `bound(…, root=True)` calls, and
the `yield depth, gamma, score, self.tp_move.get(pos)` tuple.

The pin is the FULL depth-1 bracket to convergence — three yields,
every `(depth, gamma, score, move)` tuple AND the cumulative
`self.nodes` after each step CPython-exact (the lockstep signal at
driver level): score 0 at gamma 0 is a fail-high (`score >= gamma`)
setting lower = 0, the next gamma is the bracket midpoint 34645, fails
low at 46, gamma 23 fails high at 37, and `lower (37) < upper (46) −
EVAL_ROUGHNESS (15)` is false — depth 1 converged in three probes.

**PASS 8 MOVED THE EMPTY-TRACE FRONTIER, and that is the finding.**
Pass 5 pinned FOUR yields here: the depth-2 rollover came for free
because nothing consulted the clock below node 2048. Engine master
ends every depth iteration with

    if time.time() > self.soft: return

so the driver consults the wall once per COMPLETED DEPTH, and at the
empty trace the fourth step now refuses at that consultation point
rather than at node 2048. The frontier is a statement about the
PROGRAM, not about the trace machinery, so it moved with the program;
both halves are pinned below, and the depth-2-and-deeper stepping is
`pins_clock.lean`'s seeded business. -/

private def searchGen : Option (World × Addr × Addr) :=
  match searcherW with
  | some (w, a) =>
    let histA := w.heap.size
    let w2 := { w with heap := w.heap.push (.list #[posH 0]) }
    (match callIn sunfish 4096 w2 "Searcher.search" #[.ref a, .ref histA] with
     | .ok w' (.ref g) => some (w', a, g)
     | _ => Option.none)
  | Option.none => Option.none

/-- Step the search generator `n` times: per step, the yielded
`(depth, gamma, score, move)` and `self.nodes` after the step. -/
private def searchSteps (w : World) (sa g : Addr) :
    Nat → Option (List ((Int × Int × Int × Option (Int × Int × String)) × Int))
  | 0 => some []
  | n + 1 =>
    match stepIter sunfish 1000000 w g with
    | .ok w' (some (.tuple #[.int d, .int gm, .int sc, mv])) =>
      (match Heap.get? w'.heap sa with
       | some (.instance _ attrs) =>
         (match Env.lookup attrs.toList "nodes" with
          | some (.int nn) =>
            (match (match mv with
                    | .ntuple _ _ #[.int i, .int j, .str p] => some (some (i, j, p))
                    | .none => some Option.none
                    | _ => Option.none) with
             | some mvv => (searchSteps w' sa g n).map (((d, gm, sc, mvv), nn) :: ·)
             | Option.none => Option.none)
          | _ => Option.none)
       | _ => Option.none)
    | _ => Option.none

#guard (match searchGen with
        | some (w, sa, g) => searchSteps w sa g 3
        | Option.none => Option.none) ==
  some [((1, 0, 0, some (84, 64, "")), 2),
        ((1, 34645, 46, some (84, 64, "")), 3),
        ((1, 23, 37, some (97, 76, "")), 45)]

/-- Step the generator `n` times for the WORLD alone — the frontier pin
below needs where the walk lands, not what it yielded. -/
private def stepOnly (g : Addr) : Nat → World → Option World
  | 0, w => some w
  | n + 1, w =>
    match stepIter sunfish 1000000 w g with
    | .ok w' (some _) => stepOnly g n w'
    | _ => Option.none

/-! **The fourth step refuses, at #236's own line.** Depth 1 has
converged, the `for depth in range(1, 1000)` body reaches
`if time.time() > self.soft: return`, and the EMPTY trace answers
loudly — the underrun message verbatim, at the exact consultation
point. Forty-five nodes in, not two thousand: the new frontier is
cheaper to pin than the old one. -/
#guard (match searchGen with
        | some (w, _, g) =>
          (match stepOnly g 3 w with
           | some w3 =>
             (match stepIter sunfish 1000000 w3 g with
              | .unsupported msg =>
                msg == "clock trace underrun: time.time() has no next reading (the trace is an INPUT — docs/memory-model.md §the trace clock)"
              | _ => false)
           | Option.none => false)
        | Option.none => false)

/-! After ONE step the prologue's state effects are visible in the
world: `pst["K"]` IS the live `K_MID` binding (the queens-on swap ran
through the live-view store) and `self.root` IS the root position
(the split chained assignment). -/

#guard (match searchGen with
        | some (w, sa, g) =>
          (match stepIter sunfish 1000000 w g with
           | .ok w' (some _) =>
             (match Heap.get? w'.heap sa, Env.lookup w'.globals "K_MID",
                    Env.lookup w'.globals "pst" with
              | some (.instance _ attrs), some kmid, some (.ref pa) =>
                (match Heap.get? w'.heap pa with
                 | some (.dict es _) =>
                   (dictFind es.toList (.str "K") == some kmid)
                     && (Env.lookup attrs.toList "root" == some (posH 0))
                 | _ => false)
              | _, _, _ => false)
           | _ => false)
        | Option.none => false)


end Examples.python.sunfish.pins_search
