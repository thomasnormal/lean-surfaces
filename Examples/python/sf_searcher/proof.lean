/-
Proof module for `Examples/python/sf_searcher/spec.lean` (three-file
example layout). The `CallsIn` witnesses are kernel-evaluated concrete
runs (`⟨4096, by rfl⟩` — the stateful `CallsTo.intro` analog, exactly
`sf_tt`'s route); the pinning corollary goes through
`CallsIn.functional` (fuel monotonicity at the `callIn` conjunct), and
the chained form composes the write and read witnesses at the
intermediate world.
-/
import LeanModels

namespace Examples.python.sf_searcher.proof

open LeanModels LeanModels.Python

load_program sf_searcher from "Examples/python/sf_searcher/sf_searcher.json"

private def wA : World :=
  ⟨#[.instance 0 #[]], [("MATE_UPPER", .int 69290)], []⟩

private def wB : World :=
  ⟨#[.instance 0 #[("tp_score", .ref 1), ("tp_move", .ref 2), ("nodes", .int 0)],
     .dict #[] 0, .dict #[] 0],
   [("MATE_UPPER", .int 69290)], []⟩

private def wC : World :=
  ⟨#[.instance 0 #[("tp_score", .ref 1), ("tp_move", .ref 2), ("nodes", .int 1)],
     .dict #[(.tuple #[.int 3, .int 10], .int 9)] 1,
     .dict #[(.int 3, .int 10)] 1],
   [("MATE_UPPER", .int 69290)], []⟩

private def wD : World :=
  ⟨#[.instance 0 #[("tp_score", .ref 1), ("tp_move", .ref 2), ("nodes", .int 2)],
     .dict #[(.tuple #[.int 3, .int 10], .int 9)] 1,
     .dict #[(.int 3, .int 10)] 1],
   [("MATE_UPPER", .int 69290)], []⟩

theorem searcher_init_callsIn :
    CallsIn sf_searcher wA "Searcher.__init__" #[.ref 0] wB .none :=
  ⟨4096, by rfl⟩

theorem bound_writes_callsIn :
    CallsIn sf_searcher wB "Searcher.bound" #[.ref 0, .int 3, .int 10]
      wC (.int 9) :=
  ⟨4096, by rfl⟩

theorem bound_reads_callsIn :
    CallsIn sf_searcher wC "Searcher.bound" #[.ref 0, .int 3, .int 10]
      wD (.int 9) :=
  ⟨4096, by rfl⟩

theorem bound_twice_chained :
    ∃ w₁, CallsIn sf_searcher wB "Searcher.bound" #[.ref 0, .int 3, .int 10]
            w₁ (.int 9)
        ∧ CallsIn sf_searcher w₁ "Searcher.bound" #[.ref 0, .int 3, .int 10]
            wD (.int 9) :=
  ⟨wC, bound_writes_callsIn, bound_reads_callsIn⟩

theorem bound_second_call_pinned {w' : World} {v : RVal}
    (h : CallsIn sf_searcher wC "Searcher.bound" #[.ref 0, .int 3, .int 10]
          w' v) :
    v = .int 9 ∧ w' = wD := by
  have hf := CallsIn.functional h bound_reads_callsIn
  exact ⟨hf.2, hf.1⟩

theorem visited_callsIn :
    CallsIn sf_searcher wD "Searcher.visited" #[.ref 0] wD (.int 2) :=
  ⟨4096, by rfl⟩

end Examples.python.sf_searcher.proof
