/-
sunfish pin file: the pass-4 capstone — `Searcher().bound()` END TO
END on the shipped file (the 23-pair CPython battery; node-count
equality is the lockstep signal) — and the trace-clock pins (the
2048-node frontier underrun, the armed deadline pair).

Part of the pass-7 SPEC-POLE SPLIT (docs/backlog.md §Pass 7): the
program and shared probe defs come from `pins_common.lean` — after an
envelope re-extraction, edit THAT file (the JSON trap note there); this
file rebuilds through the import.
-/
import LeanModels
import Examples.python.sunfish.pins_common

namespace Examples.python.sunfish.pins_bound

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins

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

-- (`sp0`/`searcherW` come from `pins_common.lean`)

/-- `(bound, nodes)` of one probe `Searcher().bound(pos, gamma, depth)`
— fresh searcher per probe, exactly the CPython driver. -/
private def boundProbe (pos : RVal) (gamma depth : Int) :
    Option (Int × Int) :=
  match searcherW with
  | some (w, a) =>
    (match callIn sunfish 1000000 w "Searcher.bound"
        #[.ref a, pos, .int gamma, .int depth] with
     | .ok w' (.int r) =>
       (match Heap.get? w'.heap a with
        | some (.instance _ attrs) =>
          (match Env.lookup attrs.toList "nodes" with
           | some (.int n) => some (r, n)
           | _ => Option.none)
        | _ => Option.none)
     | _ => Option.none)
  | Option.none => Option.none

/-- Midgame (Italian-shaped, after 1.e4 e5 2.Nf3 Nc6 3.Bc4 Nf6 4.d3
Bc5 — the position the side to move sees). -/
private def posMid : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str "         \n         \n r.bqk..r\n pppp.ppp\n ..n..n..\n ..b.p...\n ..B.P...\n ...P.N..\n PPP..PPP\n RNBQK..R\n         \n         \n",
      .int (-13), .tuple #[.bool true, .bool true],
      .tuple #[.bool true, .bool true], .int 0, .int 0]

/-- Tactical (a Scholar's-mate-shaped attack: the side to move has a
mate-band line — the king-capture sentinel path). -/
private def posTac : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str "         \n         \n r.bqkb.r\n pppp.ppp\n ..n..n..\n ....p..Q\n ..B.P...\n ........\n PPPP.PPP\n RNB.K.NR\n         \n         \n",
      .int (-38), .tuple #[.bool true, .bool true],
      .tuple #[.bool true, .bool true], .int 0, .int 0]

/-- Rook endgame (KRK-shaped — the mop-up/correction territory). -/
private def posEnd : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str "         \n         \n ....k...\n ........\n ....K...\n ........\n .R......\n ........\n ........\n ........\n         \n         \n",
      .int 0, .tuple #[.bool false, .bool false],
      .tuple #[.bool false, .bool false], .int 0, .int 0]

/-- Quiet pawn endgame (kings and one pawn each). -/
private def posPend : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str "         \n         \n ....k...\n .....p..\n ........\n ........\n .....P..\n ........\n ....K...\n         \n         \n         \n",
      .int 0, .tuple #[.bool false, .bool false],
      .tuple #[.bool false, .bool false], .int 0, .int 0]

-- the opening board, depths 1-3 across failing-low and failing-high windows
#guard boundProbe (posH 0) 0 1 == some (0, 2)
#guard boundProbe (posH 0) 40 1 == some (37, 34)
#guard boundProbe (posH 0) (-100) 1 == some (0, 2)
#guard boundProbe (posH 0) 0 2 == some (0, 2)
#guard boundProbe (posH 0) 40 2 == some (36, 138)
#guard boundProbe (posH 0) 0 3 == some (0, 34)
#guard boundProbe (posH 0) 40 3 == some (39, 197)
#guard boundProbe (posH 0) (-100) 3 == some ((-46), 2)

-- midgame
#guard boundProbe posMid 0 1 == some (2, 66)
#guard boundProbe posMid 60 1 == some (35, 5)
#guard boundProbe posMid 0 2 == some ((-1), 586)
#guard boundProbe posMid 60 2 == some (59, 240)
#guard boundProbe posMid 0 3 == some (2, 413)
#guard boundProbe posMid 60 3 == some (59, 240)

-- tactical: pass 7 answered MATE_LOWER exactly here; engine master
-- settles on the futility cap first (see the header)
#guard boundProbe posTac 0 2 == some (277, 3)
#guard boundProbe posTac 0 3 == some (417, 24)

-- endgames: the correction arms
#guard boundProbe posEnd 0 1 == some (111, 5)
#guard boundProbe posEnd 0 2 == some (91, 5)
#guard boundProbe posEnd 0 3 == some (0, 2)
#guard boundProbe posEnd 60 3 == some (137, 13)
#guard boundProbe posPend 0 2 == some (19, 2)
#guard boundProbe posPend 60 2 == some (50, 13)
#guard boundProbe posPend 0 3 == some (50, 14)

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

end Examples.python.sunfish.pins_bound
