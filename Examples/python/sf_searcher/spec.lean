/-
Examples/python/sf_searcher — three-file example layout. The H3 sunfish
artifact: the REAL `Searcher` class shape — `__init__` creating
`tp_score`/`tp_move` as heap dicts on `self`, `bound` mutating `self`
across calls — proved as stateful `CallsIn` facts (Surface.lean).
Methods ARE functions here: ingestion flattens them under qualified
names (`"Searcher.bound"`), so the class tier needed no new call
judgment — `self` is an ordinary `.ref` argument, exactly the
`sf_hist`/`sf_tt` machinery.

The cross-call-state acceptance behavior, as theorems — SYMBOLIC in the
position and bound: one `bound` call WRITES the transposition table
(`bound_writes_symbolic`, for every `pos ≠ 0` and every `gamma`), and a
second identical call from the resulting world READS that entry back —
same score, one more node, no insertion — with NO hypotheses at all
(`bound_reads_symbolic`: the table hit short-circuits before the mate
branch could ask about `pos`). Concrete kernel-witnessed instances and
the chained/pinned corollaries follow. `pos`/`gamma` are ints —
`Position` is a namedtuple, recorded as VALUE-like and not yet in tier
(docs/memory-model.md §H3).
-/
import Examples.python.sf_searcher.proof

open LeanModels LeanModels.Python

load_program sf_searcher from "Examples/python/sf_searcher/sf_searcher.json"

/-! Non-vacuity: concrete runs (values cross-checked against CPython —
`harness/cases.json` rows). The second `bound` is a table hit; the mate
branch (`pos == 0`) scores `-MATE_UPPER`; two searchers share nothing. -/
#py_check sf_searcher.bound_twice(5, 100) =
  (Val.tuple #[.int 99, .int 99, .int 2, .int 1])
#py_check sf_searcher.bound_twice(0, 5) =
  (Val.tuple #[.int (-69290), .int (-69290), .int 2, .int 1])
#py_check sf_searcher.bound_two_positions(1, 2, 10) =
  (Val.tuple #[.int 9, .int 9, .int 2, .int 2])
#py_check sf_searcher.fresh_searchers(3, 7) =
  (Val.tuple #[.int 6, .int 1, .int 0, .int 0])

/-- The world holding a freshly ALLOCATED (not yet initialized) Searcher
instance at address 0 — what instantiation builds just before running
`__init__`. The G1 globals carry `MATE_UPPER`; the init heap is empty
(`#guard` below), so the instance is the first object. -/
private def wA : World :=
  ⟨#[.instance 0 #[]], [("MATE_UPPER", .int 69290)], [], []⟩

/-- After `Searcher.__init__`: `self.tp_score`/`self.tp_move` are fresh
heap dicts (addresses 1 and 2 — allocated by the RHS `{}` displays
before each attribute store), `self.nodes = 0`. Mutable self on the
heap: the attribute table IS the instance object. -/
private def wB : World :=
  ⟨#[.instance 0 #[("tp_score", .ref 1), ("tp_move", .ref 2), ("nodes", .int 0)],
     .dict #[] 0, .dict #[] 0],
   [("MATE_UPPER", .int 69290)], [], []⟩

/-- After the first `bound(pos, gamma)` — PARAMETRIC in the symbolic
arguments: one node visited, the score `gamma - 1` stored under the
TUPLE key `(pos, gamma)` in `tp_score`, the move table keyed by the
position — both shape versions bumped by the insertions. -/
private def wC (p g : Int) : World :=
  ⟨#[.instance 0 #[("tp_score", .ref 1), ("tp_move", .ref 2), ("nodes", .int 1)],
     .dict #[(.tuple #[.int p, .int g], .int (g - 1))] 1,
     .dict #[(.int p, .int g)] 1],
   [("MATE_UPPER", .int 69290)], [], []⟩

/-- After the second identical `bound`: ONLY `nodes` moved — the call
was a table hit (no insertion, no shape change). -/
private def wD (p g : Int) : World :=
  ⟨#[.instance 0 #[("tp_score", .ref 1), ("tp_move", .ref 2), ("nodes", .int 2)],
     .dict #[(.tuple #[.int p, .int g], .int (g - 1))] 1,
     .dict #[(.int p, .int g)] 1],
   [("MATE_UPPER", .int 69290)], [], []⟩

#guard initWorld sf_searcher == ⟨#[], [("MATE_UPPER", .int 69290)], [], []⟩
#guard (initWorld sf_searcher).heap.push (.instance 0 #[]) == wA.heap

/-- **Stateful spec**: `__init__` transforms the bare instance into the
initialized Searcher — through `callIn` with `self` bound, like any
function. -/
theorem searcher_init_callsIn :
    CallsIn sf_searcher wA "Searcher.__init__" #[.ref 0] wB .none := by
  proofs

/-- **Stateful spec (write), SYMBOLIC**: for every non-mate position and
every bound, the first `bound` call scores the node AND leaves
`gamma - 1` in `self.tp_score` under the tuple key — the mutation is IN
the world it hands back. -/
theorem bound_writes_symbolic (p g : Int) (hp : ¬ (p = 0)) :
    CallsIn sf_searcher wB "Searcher.bound" #[.ref 0, .int p, .int g]
      (wC p g) (.int (g - 1)) := by
  proofs

/-- **The cross-call state theorem (read), SYMBOLIC and
hypothesis-free**: a second identical `bound` from the post-write world
SEES the first call's table entry for EVERY `pos`/`gamma` — the same
score comes back from the table before the mate branch could even ask
about `pos`; only `nodes` moves, nothing is inserted. -/
theorem bound_reads_symbolic (p g : Int) :
    CallsIn sf_searcher (wC p g) "Searcher.bound" #[.ref 0, .int p, .int g]
      (wD p g) (.int (g - 1)) := by
  proofs

/-- Chained form: from the initialized Searcher, calling `bound` twice
threads through the intermediate world — "the second call sees the
first call's write" as one symbolic statement. -/
theorem bound_twice_chained (p g : Int) (hp : ¬ (p = 0)) :
    ∃ w₁, CallsIn sf_searcher wB "Searcher.bound" #[.ref 0, .int p, .int g]
            w₁ (.int (g - 1))
        ∧ CallsIn sf_searcher w₁ "Searcher.bound" #[.ref 0, .int p, .int g]
            (wD p g) (.int (g - 1)) := by
  proofs

/-- Concrete kernel-witnessed instance of the write half (the
`#py_check` analog at the stateful judgment). -/
theorem bound_writes_callsIn :
    CallsIn sf_searcher wB "Searcher.bound" #[.ref 0, .int 3, .int 10]
      (wC 3 10) (.int 9) := by
  proofs

/-- Any decided second call is PINNED to the table hit (`CallsIn` is
functional across fuels): result `gamma - 1`, world `wD p g` — nothing
else can happen. -/
theorem bound_second_call_pinned (p g : Int) {w' : World} {v : RVal}
    (h : CallsIn sf_searcher (wC p g) "Searcher.bound" #[.ref 0, .int p, .int g]
          w' v) :
    v = .int (g - 1) ∧ w' = wD p g := by
  proofs

/-- Argument-less method through the same machinery: `visited` reads
`self.nodes` and returns the world untouched. -/
theorem visited_callsIn (p g : Int) :
    CallsIn sf_searcher (wD p g) "Searcher.visited" #[.ref 0]
      (wD p g) (.int 2) := by
  proofs
