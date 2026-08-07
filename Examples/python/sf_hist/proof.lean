/-
Proof module for `Examples/python/sf_hist/spec.lean` (three-file example
layout). The concrete `CallsIn` witnesses are kernel-evaluated runs
(`⟨4096, by rfl⟩`, the sf_tt idiom); the value-symbolic aliasing theorem
walks the run with `py_simp` at a fixed small fuel — the heap operations
(`Heap.get?`/`Heap.update`, `heapStore`/`heapIndex` through `List.set`)
are list-structural, so they reduce with a symbolic element in place;
`rotate_scores_functional` pins any decided outcome through
`CallsIn.functional`.
-/
import LeanModels

namespace Examples.python.sf_hist.proof

open LeanModels LeanModels.Python

load_program sf_hist from "Examples/python/sf_hist/sf_hist.json"

private def wA : World := ⟨#[.list #[.int 5]], [], []⟩
private def wB : World := ⟨#[.list #[.int 5, .int 6]], [], []⟩
private def wOne : World := ⟨#[.list #[.int 1, .int 2]], [], []⟩
private def wOne' : World := ⟨#[.list #[.int 99, .int 2]], [], []⟩
private def wTwo : World :=
  ⟨#[.list #[.int 1, .int 2], .list #[.int 1, .int 2]], [], []⟩
private def wTwo' : World :=
  ⟨#[.list #[.int 99, .int 2], .list #[.int 1, .int 2]], [], []⟩

theorem push_callsIn :
    CallsIn sf_hist wA "push" #[.ref 0, .int 6] wB (.int 2) :=
  ⟨4096, by rfl⟩

theorem current_callsIn :
    CallsIn sf_hist wB "current" #[.ref 0] wB (.int 6) :=
  ⟨4096, by rfl⟩

theorem poke_first_aliased :
    CallsIn sf_hist wOne "poke_first" #[.ref 0, .ref 0] wOne' (.int 99) :=
  ⟨4096, by rfl⟩

theorem poke_first_distinct :
    CallsIn sf_hist wTwo "poke_first" #[.ref 0, .ref 1] wTwo' (.int 1) :=
  ⟨4096, by rfl⟩

theorem poke_first_aliased_symbolic (n : Int) :
    CallsIn sf_hist ⟨#[.list #[.int n, .int 0]], [], []⟩ "poke_first"
      #[.ref 0, .ref 0] ⟨#[.list #[.int 99, .int 0]], [], []⟩ (.int 99) := by
  refine ⟨32, ?_⟩
  rw [callIn]
  py_simp [sf_hist]

theorem rotate_scores_callsIn :
    CallsIn sf_hist ⟨#[.list #[.int 1, .int (-2), .int 3]], [], []⟩
      "rotate_scores" #[.ref 0]
      ⟨#[.list #[.int (-1), .int 2, .int (-3)]], [], []⟩ .none :=
  ⟨4096, by rfl⟩

theorem rotate_scores_functional {w' : World} {v : RVal}
    (h : CallsIn sf_hist ⟨#[.list #[.int 1, .int (-2), .int 3]], [], []⟩
      "rotate_scores" #[.ref 0] w' v) :
    v = .none ∧ w' = ⟨#[.list #[.int (-1), .int 2, .int (-3)]], [], []⟩ := by
  have hf := CallsIn.functional h rotate_scores_callsIn
  exact ⟨hf.2, hf.1⟩

end Examples.python.sf_hist.proof
