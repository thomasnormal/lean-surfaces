/-
sunfish pin file: the ∀-TRACE transport at search scale — the pass-7
CLOCK-ERASURE payoff (docs/memory-model.md §clock erasure). The
pass-5/6 pins ran at the EMPTY clock trace; `boundProbeT_all_traces`
below transports ANY decided empty-trace probe to EVERY seeded trace
(`ClockTrace.WallClock` — no side condition), composing the
`evalExpr`/`callIn` erasure conjuncts through the probe's projections.

THE MEASURED BOUNDARY (recorded in the §clock erasure as-built notes):
discharging a search-scale empty-trace hypothesis AS A THEOREM needs a
kernel run whose cost is dominated by `initWorld` — one 2-node probe
exceeded 16 minutes of `decide +kernel`, versus ~seconds under the
UNTRUSTED evaluator that `#guard` actually uses (its own docstring:
passing "is *not* a proof"). So this file lands the transport THEOREM
(seconds to check, reusable for every probe) plus NATIVE `#guard` pins
of the seeded surface — the same trust level as the entire existing
pin battery — and the unconditional search-scale `∀ tr` THEOREM waits
on a kernel-affordable concrete-run route (open, backlog).
`clock_lab.pure_sum_all_traces_transported` remains the unconditional
exemplar of the transport at symbolic-execution scale.

Part of the pass-7 SPEC-POLE SPLIT: the program and shared probe defs
come from `pins_common.lean` — after an envelope re-extraction, edit
THAT file; this file rebuilds through the import.
-/
import LeanModels
import Examples.python.sunfish.pins_common

namespace Examples.python.sunfish.pins_clock

open LeanModels LeanModels.Python
open Examples.python.sunfish.pins

/-- `Searcher()` constructed from `initWorld` with the clock trace
seeded BEFORE anything runs — the `∀ tr` twin of `pins.searcherW`. -/
def searcherWT (tr : ClockTrace) : Option (World × Addr) :=
  match evalExpr sunfish 4096 ⟨(initWorld sunfish).withClock tr, []⟩
      (.call (.name "Searcher" sp0) #[] #[] Option.none sp0) with
  | .ok st (.ref a) => some (st.world, a)
  | _ => Option.none

/-- `(bound, nodes)` of one probe under a seeded trace — the `∀ tr`
twin of the battery's `boundProbe` (pins_bound.lean). -/
def boundProbeT (tr : ClockTrace) (pos : RVal) (gamma depth : Int) :
    Option (Int × Int) :=
  match searcherWT tr with
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

/-- **The transport**: a probe decided at the EMPTY trace answers the
same pair under EVERY seeded trace — `evalExpr`/`callIn` clock erasure
composed through the probe's projections (heap reads never see the
clock). -/
theorem boundProbeT_all_traces {pos : RVal} {gamma depth : Int}
    {p : Int × Int} (h : boundProbeT [] pos gamma depth = some p)
    (tr : ClockTrace) : boundProbeT tr pos gamma depth = some p := by
  unfold boundProbeT searcherWT at h ⊢
  rw [World.withClock_self (initWorld_clock sunfish)] at h
  obtain ⟨hok, -, -⟩ :=
    evalExpr_clockErased 4096 sunfish ⟨initWorld sunfish, []⟩
      (.call (.name "Searcher" sp0) #[] #[] Option.none sp0)
      (initWorld_clock sunfish)
  cases hrun : evalExpr sunfish 4096 ⟨initWorld sunfish, []⟩
      (.call (.name "Searcher" sp0) #[] #[] Option.none sp0) with
  | ok st v =>
    obtain ⟨hst, hy⟩ := hok st v hrun
    simp only [FrameState.withClock_mk] at hy
    rw [hrun] at h
    simp only [hy]
    cases v <;> try (simp_all)
    case ref a =>
      try simp only [FrameState.withClock_world, FrameState.withClock_locals,
        World.withClock_heap, World.withClock_globals]
      obtain ⟨hok2, -, -⟩ :=
        callIn_clockErased 1000000 sunfish st.world "Searcher.bound"
          #[.ref a, pos, .int gamma, .int depth] hst
    -- the base h reduced to the callIn match at st.world
      cases hci : callIn sunfish 1000000 st.world "Searcher.bound"
          #[.ref a, pos, .int gamma, .int depth] with
      | ok w' rv =>
        obtain ⟨hw', hy2⟩ := hok2 w' rv hci
        rw [hci] at h
        simp only [hy2]
        cases rv <;> simp_all
      | exn w' e => rw [hci] at h; simp at h
      | timeout => rw [hci] at h; simp at h
      | unsupported msg => rw [hci] at h; simp at h
  | exn st e => rw [hrun] at h; simp at h
  | timeout => rw [hrun] at h; simp at h
  | unsupported msg => rw [hrun] at h; simp at h

/-! ### The seeded surface, pinned natively

`boundProbeT []` agrees with the battery's `boundProbe` rows
(pins_bound.lean) — the `[]`-boundary sanity — and a NONEMPTY trace
answers the same pairs, the transport's content sampled on concrete
traces (all `#guard`: the untrusted evaluator, the batteries' standing
trust level; the theorem above is what upgrades any of these to
`∀ tr` the moment its empty-trace instance is proved). -/

#guard boundProbeT [] (posH 0) 0 1 == some (0, 2)
#guard boundProbeT [123] (posH 0) 0 1 == some (0, 2)
#guard boundProbeT [7, 8, 9] (posH 0) 40 1 == some (37, 35)

/-- Tactical (the mate band — the king-capture sentinel path). -/
private def posTacC : RVal :=
  .ntuple "Position" #["board", "score", "wc", "bc", "ep", "kp"]
    #[.str "         \n         \n r.bqkb.r\n pppp.ppp\n ..n..n..\n ....p..Q\n ..B.P...\n ........\n PPPP.PPP\n RNB.K.NR\n         \n         \n",
      .int (-38), .tuple #[.bool true, .bool true],
      .tuple #[.bool true, .bool true], .int 0, .int 0]

#guard boundProbeT [] posTacC 0 2 == some (47923, 4)
#guard boundProbeT [55] posTacC 0 2 == some (47923, 4)

/-! ### DEEPER STEPPING THROUGH THE WALL (the pass-7 close of the
pass-5 frontier): `search()` stepped to depth 4 under a SEEDED trace

The pass-5 capstone stopped at four yields — the 2048-node wall stood
between depth 2 and everything deeper, and the empty trace refuses
there loudly. THE TRACE CLOCK opens it: with ONE seeded reading the
stepping crosses node 2048 inside step 12 (depth 4's first yield,
CPython consults `time.time()` exactly once against
`deadline = 1 << 63` and continues), and every `(depth, gamma, score,
move)` tuple AND cumulative `self.nodes` below is CPython's own answer
(the counting-clock oracle: integer reading 0, calls counted — steps
1–11 consume NOTHING, step 12 consumes exactly the one reading).
Both directions are pinned: at `[]` the 12th step refuses with the
underrun message at the exact consultation point; at `[0]` it
continues to CPython's `(4, 33, 32, g8f6)` with the trace consumed. -/

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

-- ONE PASS pins everything: steps 1–11 (depth-1/2/3 brackets to
-- convergence — tuples and nodes CPython-exact) leave the trace
-- UNTOUCHED (`w11.clock == [0]`: no consultation below node 2048), and
-- step 12 — depth 4's first yield — crosses node 2048, consults the
-- clock ONCE and continues to CPython's (4, 33, 32, g8f6) with the
-- reading CONSUMED (`w12.clock.isEmpty`). The consumption is the
-- positive proof the consultation happened at the wall; the loud
-- direction (the empty trace refusing at the same consultation point)
-- is pinned at bound() level by pins_bound.lean's nodes-2047 frontier
-- probe — one node in, never a 2048-node walk per build.
#guard (match searchGenT [0] with
        | some (w, sa, g) =>
          (match searchStepsW sa g 11 w with
           | some (rows, w11) =>
             rows ==
               [((1, 0, 0, some (84, 64, "")), 2),
                ((1, 34645, 46, some (84, 64, "")), 4),
                ((1, 23, 37, some (97, 76, "")), 47),
                ((2, 42, 41, some (97, 76, "")), 93),
                ((2, -34624, -9, some (97, 76, "")), 96),
                ((2, 16, 13, some (97, 76, "")), 334),
                ((2, 2, 4, some (97, 76, "")), 347),
                ((3, 9, 11, some (97, 76, "")), 466),
                ((3, 34651, 46, some (97, 76, "")), 509),
                ((3, 29, 29, some (97, 76, "")), 703),
                ((3, 38, 36, some (97, 76, "")), 803)]
               && w11.clock == [0]
               && (match searchStepsW sa g 1 w11 with
                   | some (rows12, w12) =>
                     rows12 == [((4, 33, 32, some (97, 76, "")), 2073)]
                       && w12.clock.isEmpty
                   | Option.none => false)
           | Option.none => false)
        | Option.none => false)

end Examples.python.sunfish.pins_clock
