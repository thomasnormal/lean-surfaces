/-
**THE FAIL-LOW ARM'S CENSUS** — the six questions docs/backlog.md §L27 owes
before a premise of the second induction is written, answered BY MEASUREMENT on
the shipped engine (§L24's exit law; §L25's law 1, *run it on the fixture and
compare, before writing `= .ok ⟨w, e⟩ v`*, and law 2, *measure the fuel*).

Its own file for the throughput law (§L29): every number below runs the shipped
`bound()`, and `basecase_depth0.lean` is already 63 s.

**Nothing here is proved.** Every declaration is a `#guard` or the computation a
`#guard` reads. The point is that §L30's plan quotes numbers that cannot rot: a
re-pin of the envelope moves the guards with it, and a plan premise that stops
being true stops building.

The reference point is §L27's own — `bd_probe (posH 0) 40 0 = some (4, 34)`, one
depth-0 call writing thirty-four keys, all of them at depth 0
(`qs_child_depth_eq`). That is the circularity as data.
-/
import Examples.python.sunfish.basecase_depth0

namespace Examples.python.sunfish.faillow_census

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins
open Examples.python.sunfish.genmoves_theorem (posOf)
open Examples.python.sunfish.bound_depth
open Examples.python.sunfish.basecase_depth0

set_option maxRecDepth 100000

/-! ## §1 One probe, six numbers — so each fixture costs ONE run

A 34-node `bound()` costs ~13 s to elaborate, so the battery reads everything it
wants out of a single call: the answer, the node counter, the size of `tp_score`
and of `tp_move`, and the heap on both sides. -/
private def probe (pos : RVal) (gamma : Int) : Option (Int × Int × Nat × Nat × Nat × Nat) :=
  match searcherW with
  | some (w, a) =>
    (match callIn sunfish 1000000 w "Searcher.bound" #[.ref a, pos, .int gamma, .int 0] with
     | .ok w' (.int r) =>
       (match Heap.get? w'.heap a with
        | some (.instance _ attrs) =>
          (match Env.lookup attrs.toList "nodes", Env.lookup attrs.toList "tp_score",
                 Env.lookup attrs.toList "tp_move" with
           | some (.int n), some (.ref ts), some (.ref tm) =>
             (match Heap.get? w'.heap ts, Heap.get? w'.heap tm with
              | some (.dict es _), some (.dict ms _) =>
                some (r, n, es.size, ms.size, w.heap.size, w'.heap.size)
              | _, _ => Option.none)
           | _, _, _ => Option.none)
        | _ => Option.none)
     | _ => Option.none)
  | Option.none => Option.none

/-- One ply of the shipped `Position.move` — the `value_bound.lean` pattern, so
no board below is invented. -/
private def ply (p : Option RVal) (i j : Int) : Option RVal :=
  match p with
  | some p0 =>
    (match callIn sunfish 256 (initWorld sunfish) "Position.move" #[p0, mvOf i j ""] with
     | .ok _ v => some v
     | _ => Option.none)
  | none => Option.none

private def boardOf (p : Option RVal) : String :=
  match p with
  | some (.ntuple _ _ #[.str b, _, _, _, _, _]) => b
  | _ => ""

/-! ## §2 THE TWO ARMS, side by side

The cut is one node and four allocations; the fail-low arm is thirty-four nodes
and 2811. Both leave `tp_move` EMPTY, which is §6's point. -/
#guard probe (posH 0) 0 == some (0, 1, 1, 0, 70, 74)
#guard probe (posH 0) 40 == some (4, 34, 34, 0, 70, 2881)

/-! ## §3 Q6 — ONE depth-0 CHILD call, measured FIRST

§L27's sixth question, and the exit law's own instruction. At `gamma = 40` the
parent searches the two moves that clear the QS floor, each at the NEGATED window
`1 - 40 = -39`, so these are the calls an induction hypothesis has to cover. -/

/-- The boards after `1. d4` and `1. e4`, cached as literals and pinned to the
plies below — a nullary `def` is re-evaluated by every `#guard` that names it
(§L28's third finding). Note the leading newline: this is the residue's own
spelling for a ROTATED board, copied and not tidied. -/
private def d4B : String :=
  "\n         \n         \nrnbkqbnr \npppp.ppp \n........ \n....p... \n........ \n........ \nPPPPPPPP \nRNBKQBNR \n         \n         "
private def e4B : String :=
  "\n         \n         \nrnbkqbnr \nppp.pppp \n........ \n...p.... \n........ \n........ \nPPPPPPPP \nRNBKQBNR \n         \n         "

/-- …and the `ep` squares are the ENGINE's: `119 - (84 + 64) / 2 = 45` and
`119 - (85 + 65) / 2 = 44`. -/
private def d4Pos : RVal := posOf d4B (-46) true true true true 45 0
private def e4Pos : RVal := posOf e4B (-42) true true true true 44 0

#guard ply (some (posH 0)) 84 64 == some d4Pos
#guard ply (some (posH 0)) 85 65 == some e4Pos
#guard d4B.length == 120 && e4B.length == 120

/-! **And a depth-0 child is NOT a leaf.** Six nodes and twenty-seven, from one
ply of the reference position — the induction hypothesis the fail-low arm
consumes is a run of exactly the same shape as the run it is proving. -/
#guard probe d4Pos (-39) == some (-4, 6, 6, 0, 70, 595)
#guard probe e4Pos (-39) == some (0, 27, 27, 0, 70, 2266)

/-! **The fuel for one child, MEASURED** (§L25's law 2). 403 decides the
six-node call and 402 refuses it. Nothing in the plan may pin this numeral — it
is here so that a threshold form written later is honest about its order. -/
private def childOk (F : Nat) : Bool :=
  match searcherW with
  | some (w, a) =>
    (match callIn sunfish F w "Searcher.bound" #[.ref a, d4Pos, .int (-39), .int 0] with
     | .ok _ (.int _) => true
     | _ => false)
  | Option.none => false

#guard childOk 403
#guard !childOk 402

/-! ## §4 Q2 — THE MEASURE, and both of §L27's first two candidates are REFUTED

§L27 names three candidates: the number of pieces, the count of moves passing
the `>= QS` filter, and `formal/`'s own fuel. The first two die on the reference
fixture itself; the third dies in `formal/` (§L30 — `fuelValueD2`'s `Nat` is
remaining DEPTH, and its depth-0 clause is a static leaf with no recursion at
all). -/

/-- Candidate one. -/
private def pieceCount (b : String) : Nat := (b.toList.filter Char.isAlpha).length

private def pstRowOf (c : String) : Option (Array RVal) :=
  match Env.lookup (initWorld sunfish).globals "pst" with
  | some (.ref pa) =>
    (match Heap.get? (initWorld sunfish).heap pa with
     | some (.dict es _) =>
       (match dictFind es.toList (.str c) with
        | some (.tuple xs) => some xs
        | _ => Option.none)
     | _ => Option.none)
  | _ => Option.none

private def pstAt (c : String) (sq : Nat) : Int :=
  match pstRowOf c with
  | some xs => (match xs[sq]?.getD .none with | .int z => z | _ => 0)
  | none => 0

/-- **The candidate that survives.** The shipped `pst` summed over BOTH sides —
the mover at its own square, the opponent mirrored. It is `pos.score`'s
companion: the score is the two sides' DIFFERENCE and this is their SUM. And it
is a function of the BOARD alone — no window, no score, no table — which is the
answer to §L27's third question as well. -/
private def pstTotal (b : String) : Int :=
  b.toList.zipIdx.foldl (fun acc p =>
    if p.1.isUpper then acc + pstAt (String.singleton p.1) p.2
    else if p.1.isLower then acc + pstAt (String.singleton p.1.toUpper) (119 - p.2)
    else acc) 0

/-! **Candidate 1, `pieces`, REFUTED where it matters most — on the reference
fixture.** Both admitted moves out of the opening position are QUIET, so the
parent and both children carry thirty-two pieces and the count does not move.
Eleven of the reference run's thirty-three edges are like this (§L30). -/
#guard pieceCount board0 == 32
#guard pieceCount d4B == 32
#guard pieceCount e4B == 32

/-- Candidate two, RUN rather than asserted: `gen_moves` drained, then the
ordering genexp at `depth = 0` drained on top of it — §L29's `fxDrain`, at an
arbitrary position. -/
private def streamAt (pos : RVal) (F : Nat) : Option (Nat × Nat) :=
  match callIn sunfish F (initWorld sunfish) "Position.gen_moves" #[pos] with
  | .ok w (.ref a) =>
    (match drainIter sunfish F w a with
     | .ok _ all =>
       (match callIn sunfish F w "<genexpr@1>" #[.ref a, .int 0, pos] with
        | .ok w' (.ref b) =>
          (match drainIter sunfish F w' b with
           | .ok _ adm => some (all.length, adm.length)
           | _ => Option.none)
        | _ => Option.none)
     | _ => Option.none)
  | _ => Option.none

/-! **Candidate 2, the admitted-stream length, REFUTED beside it.** Twenty moves
generated and two admitted at the parent — and twenty and two at EACH child.
`2 → 2`, no descent anywhere. -/
#guard streamAt (posH 0) 512 == some (20, 2)
#guard streamAt d4Pos 512 == some (20, 2)
#guard streamAt e4Pos 512 == some (20, 2)

/-! **And the survivor, measured.** `pstTotal` rises by EXACTLY the move's own
`Position.value` across a quiet move — 46 and 42, the two values §L29 drained —
so the pair `(pieceCount, -pstTotal)` strictly descends on both edges where
`pieceCount` alone stands still. A capture is the other case and it descends in
the first component instead. -/
#guard pstTotal board0 == 127158
#guard pstTotal d4B == 127204
#guard pstTotal e4B == 127200
#guard pstTotal d4B - pstTotal board0 == 46
#guard pstTotal e4B - pstTotal board0 == 42

/-! ## §5 Q4 — the EXHAUSTION terminal IS reachable at depth 0

§L25's R3 notes that at depth ≥ 1 `Inv []` is no longer `False`. It is not
`False` here either: five of the reference run's thirty-four nodes admit no move
at all, so `moves()` runs out after the stand-pat and the fold's `ran` terminal
fires. Fourteen of the thirty-four reach it one way or another (§L30). -/

/-- The first such node, reached by FOUR of the search's own admitted edges —
`(84,64) (85,65) (85,65) (65,54)` — so it is a position the fail-low arm really
visits and not one written down here. -/
private def emptyB : String :=
  "         \n         \n rnbqkbnr\n ppp.pppp\n ........\n ........\n ...Pp...\n ........\n PPP..PPP\n RNBQKBNR\n         \n         \n"
private def emptyPos : RVal := posOf emptyB (-69) true true true true 0 0

#guard ply (ply (ply (ply (some (posH 0)) 84 64) 85 65) 85 65) 65 54 == some emptyPos
#guard boardOf (some emptyPos) == emptyB

/-! **And it answers the STAND-PAT exactly**, in one node: nothing clears the QS
floor, the fold consumes the single stand-pat round and exhausts, and `best` is
`pos.score`. That number is the model's own depth-0 leaf — `qsStrat`'s fourth
clause and `fuelValueD2`'s zero clause both read `eval p` — and the coincidence
is what §L30's F3 is built on. -/
#guard probe emptyPos (-29) == some (-69, 1, 1, 0, 70, 154)

/-! ## §6 Q5 — the KILLER fires in the fail-low arm, and never writes itself

The killer store is depth-GATED (`if move is not None and depth`), so a pure
depth-0 search never writes `tp_move`: every run above leaves it at size ZERO,
which is the fourth component of each tuple. A killer at a depth-0 node can
therefore only arrive from OUTSIDE — which is exactly what `BoundWF.killer`
permits, and what makes §10's `killer_reads` load-bearing rather than defensive.

Its admission ceiling at depth 0 is `val >= QS` and, since `depth` is falsy and
`depth > 3` fails, `val >= MATE_LOWER or pos.score + val >= gamma`. Both of the
opening position's admitted moves clear it at `gamma = 40`, so a seeded killer
IS yielded — ahead of the sorted stream, and again inside it. -/
#guard decide (40 ≤ (46 : Int)) && decide (0 + 46 ≥ (40 : Int))
#guard decide (40 ≤ (42 : Int)) && decide (0 + 42 ≥ (40 : Int))

/-! ## §7 What the arithmetic already gives the fail-low arm

`Report gamma best value`'s fail-low disjunct is `best < gamma ∧ value ≤ best`.
The reference run answers `4` at `gamma = 40` against a stand-pat of `0`, and the
exhausted node answers its own `-69`. In both the answer is AT OR ABOVE the
stand-pat and BELOW the window — which is `Report`'s left disjunct discharged by
arithmetic, with no child report anywhere in it. That is the census answer that
re-prices F3. -/
/-- `Report` as a `Bool`, so the battery can read it — and the one two-line
proof in the file, because a Bool mirror that drifts from the `Prop` would make
every guard below say nothing. -/
private def reportB (gamma report value : Int) : Bool :=
  (decide (report < gamma) && decide (value ≤ report))
    || (decide (gamma ≤ report) && decide (report ≤ value))

theorem reportB_iff (gamma report value : Int) :
    reportB gamma report value = true ↔ Report gamma report value := by
  simp [reportB, Report]

#guard reportB 40 4 0
#guard reportB (-29) (-69) (-69)
#guard !reportB 40 (-69) 100

#print axioms reportB_iff

end Examples.python.sunfish.faillow_census
