/-
sunfish pin shard: the TRACE-CLOCK frontier — the 2048-node underrun
and the armed-deadline pair.

SHARD of the `pins_bound` battery (2026-08-25 topology change): the
capstone prose, and the map of which board lives in which shard, are in
`pins_bound.lean`. Nothing here is new — every `#guard` moved VERBATIM
from that file, and the shard boundary is by POSITION so a red names its
board. `boundProbe` moved to `pins_common.lean` unchanged.
-/
import LeanModels
import Examples.python.sunfish.pins_common

namespace Examples.python.sunfish.pins_bound_searcher

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins

/-! ### The wall-clock frontier under THE TRACE CLOCK (pass 6)

Post-#158 `time.time()` is dynamically LIVE: `bound()` evaluates it
whenever `self.nodes % 2048 == 0`. Pass 6 made time an INPUT
(memory-model §the trace clock): the call POPS the world's clock
trace; the EMPTY trace refuses loudly at that exact consultation
point — the pass-5 frontier pin's shape, with the underrun message
(the pinned battery rows above never reach the wall: max 587 nodes,
no reading consumed). The frontier is pinned CHEAPLY as before: a
searcher whose `nodes` is pre-set to 2047, so the very NEXT entry is
the 2048th — one node in, never a 2048-node fresh run per build. And
the wall now OPENS: the armed pair below (deadline pre-set through
`Heap.update` like `nodes`; readings CPython-derived) pins BOTH
directions — a reading `≤ deadline` continues to CPython's exact
`(bound, nodes) = (0, 2049)` with the trace consumed, a reading
`> deadline` raises `Stop` at node 2048 with the world retained,
exactly where CPython stops (the raise-through-the-clock composition
with the pass-4 exceptions tier, on the shipped file). -/

private def searcherAt2047 : Option (World × Addr) :=
  match searcherW with
  | some (w, a) =>
    (match Heap.get? w.heap a with
     | some (.instance cid attrs) =>
       (match Heap.update w.heap a (.instance cid (attrs.map
            (fun p => if p.1 == "nodes" then (p.1, RVal.int 2047) else p))) with
        | some h' => some ({ w with heap := h' }, a)
        | Option.none => Option.none)
     | _ => Option.none)
  | Option.none => Option.none

#guard (match searcherAt2047 with
        | some (w, a) =>
          (match callIn sunfish 1000000 w "Searcher.bound"
              #[.ref a, posH 0, .int 0, .int 1] with
           | .unsupported msg =>
             msg == "clock trace underrun: time.time() has no next reading (the trace is an INPUT — docs/memory-model.md §the trace clock)"
           | _ => false)
        | Option.none => false)

/-- The 2047-searcher with an ARMED deadline (both attributes pre-set
through `Heap.update` — the pass-5 frontier trick): the very next
entry is the 2048th, where the guard consults the clock against
`deadline`. -/
private def searcherArmed (nodes deadline : Int) : Option (World × Addr) :=
  match searcherW with
  | some (w, a) =>
    (match Heap.get? w.heap a with
     | some (.instance cid attrs) =>
       (match Heap.update w.heap a (.instance cid (attrs.map
            (fun p => if p.1 == "nodes" then (p.1, RVal.int nodes)
                      else if p.1 == "deadline" then (p.1, RVal.int deadline)
                      else p))) with
        | some h' => some ({ w with heap := h' }, a)
        | Option.none => Option.none)
     | _ => Option.none)
  | Option.none => Option.none

-- reading 999 ≤ deadline 1000: the 2048th node consults the clock and
-- CONTINUES — the whole depth-1 bound completes, CPython-exact
-- ((0, 2049): 2047 pre-set + the 2 nodes of the fresh depth-1 probe),
-- the reading consumed (`w'.clock = []`)
#guard (match searcherArmed 2047 1000 with
        | some (w, a) =>
          (match callIn sunfish 1000000 { w with clock := [999] }
              "Searcher.bound" #[.ref a, posH 0, .int 0, .int 1] with
           | .ok w' (.int r) =>
             r == 0
               && (match Heap.get? w'.heap a with
                   | some (.instance _ attrs) =>
                     Env.lookup attrs.toList "nodes" == some (.int 2049)
                   | _ => false)
               && w'.clock.isEmpty
           | _ => false)
        | Option.none => false)

-- reading 1001 > deadline 1000: `raise Stop` fires at node 2048 — the
-- model raises at the SAME node CPython does, the world retained on
-- `.exn` (the H1 covenant), the reading consumed
#guard (match searcherArmed 2047 1000 with
        | some (w, a) =>
          (match callIn sunfish 1000000 { w with clock := [1001] }
              "Searcher.bound" #[.ref a, posH 0, .int 0, .int 1] with
           | .exn w' (.user _ nm) =>
             nm == "Stop"
               && (match Heap.get? w'.heap a with
                   | some (.instance _ attrs) =>
                     Env.lookup attrs.toList "nodes" == some (.int 2048)
                   | _ => false)
               && w'.clock.isEmpty
           | _ => false)
        | Option.none => false)

end Examples.python.sunfish.pins_bound_searcher
