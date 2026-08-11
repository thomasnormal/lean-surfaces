/-
Proof module for `Examples/python/sf_searcher/spec.lean` (three-file
example layout). The SYMBOLIC write/read pair runs one `rw [callIn.eq_2]`
step and symbolically executes the method body with `py_simp`
(`execAttrCall` passed explicitly — bound's body has no nested Python
call, so full unfolding of the dispatch is safe; the cache hit decides by
`keyEq` reflexivity — `p == p && g == g` — which is why the read theorem
needs NO hypotheses). The `__init__` and concrete witnesses are
kernel-evaluated runs (`⟨4096, by rfl⟩`, `sf_tt`'s route); the pinning
corollary goes through `CallsIn.functional` (fuel monotonicity at the
`callIn` conjunct); the chained form composes write and read at the
intermediate world. NOTE the whole-driver route (unfolding `callFunction`
plus four nested `callIn`s in one `py_simp`) whnf-storms — the per-call
`callIn.eq_2` geometry is the recorded pattern.
-/
import LeanModels

namespace Examples.python.sf_searcher.proof

open LeanModels LeanModels.Python

load_program sf_searcher from "Examples/python/sf_searcher/sf_searcher.json"

private def wA : World :=
  ⟨#[.instance 0 #[]], [("MATE_UPPER", .int 69290)], [], []⟩

private def wB : World :=
  ⟨#[.instance 0 #[("tp_score", .ref 1), ("tp_move", .ref 2), ("nodes", .int 0)],
     .dict #[] 0, .dict #[] 0],
   [("MATE_UPPER", .int 69290)], [], []⟩

private def wC (p g : Int) : World :=
  ⟨#[.instance 0 #[("tp_score", .ref 1), ("tp_move", .ref 2), ("nodes", .int 1)],
     .dict #[(.tuple #[.int p, .int g], .int (g - 1))] 1,
     .dict #[(.int p, .int g)] 1],
   [("MATE_UPPER", .int 69290)], [], []⟩

private def wD (p g : Int) : World :=
  ⟨#[.instance 0 #[("tp_score", .ref 1), ("tp_move", .ref 2), ("nodes", .int 2)],
     .dict #[(.tuple #[.int p, .int g], .int (g - 1))] 1,
     .dict #[(.int p, .int g)] 1],
   [("MATE_UPPER", .int 69290)], [], []⟩

theorem searcher_init_callsIn :
    CallsIn sf_searcher wA "Searcher.__init__" #[.ref 0] wB .none :=
  ⟨4096, by rfl⟩

set_option maxRecDepth 4096 in
theorem bound_writes_symbolic (p g : Int) (hp : ¬ (p = 0)) :
    CallsIn sf_searcher wB "Searcher.bound" #[.ref 0, .int p, .int g]
      (wC p g) (.int (g - 1)) := by
  refine ⟨64, ?_⟩
  rw [callIn.eq_2]
  py_simp [sf_searcher, execAttrCall, wB, wC, hp]

set_option maxRecDepth 4096 in
theorem bound_reads_symbolic (p g : Int) :
    CallsIn sf_searcher (wC p g) "Searcher.bound" #[.ref 0, .int p, .int g]
      (wD p g) (.int (g - 1)) := by
  refine ⟨64, ?_⟩
  rw [callIn.eq_2]
  py_simp [sf_searcher, execAttrCall, wC, wD]

theorem bound_twice_chained (p g : Int) (hp : ¬ (p = 0)) :
    ∃ w₁, CallsIn sf_searcher wB "Searcher.bound" #[.ref 0, .int p, .int g]
            w₁ (.int (g - 1))
        ∧ CallsIn sf_searcher w₁ "Searcher.bound" #[.ref 0, .int p, .int g]
            (wD p g) (.int (g - 1)) :=
  ⟨wC p g, bound_writes_symbolic p g hp, bound_reads_symbolic p g⟩

theorem bound_writes_callsIn :
    CallsIn sf_searcher wB "Searcher.bound" #[.ref 0, .int 3, .int 10]
      (wC 3 10) (.int 9) :=
  ⟨4096, by rfl⟩

theorem bound_second_call_pinned (p g : Int) {w' : World} {v : RVal}
    (h : CallsIn sf_searcher (wC p g) "Searcher.bound" #[.ref 0, .int p, .int g]
          w' v) :
    v = .int (g - 1) ∧ w' = wD p g := by
  have hf := CallsIn.functional h (bound_reads_symbolic p g)
  exact ⟨hf.2, hf.1⟩

set_option maxRecDepth 4096 in
theorem visited_callsIn (p g : Int) :
    CallsIn sf_searcher (wD p g) "Searcher.visited" #[.ref 0]
      (wD p g) (.int 2) := by
  refine ⟨64, ?_⟩
  rw [callIn.eq_2]
  py_simp [sf_searcher, execAttrCall, wD]

end Examples.python.sf_searcher.proof
