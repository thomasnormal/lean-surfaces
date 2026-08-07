/-
Examples/python/sf_tt — three-file example layout. Acceptance case 15
(docs/memory-model.md) and the FIRST stateful-judgment proofs: a
module-global dict (the transposition-table shape of sunfish's
`Searcher`) mutated by one nested call and read by the next, all inside
one shared world — stated with `CallsIn` (Surface.lean), the heap-aware
call judgment. `CallsIn` has no surface sugar yet (deliberate: the
stateful surface design is H2 work), so these statements are raw —
before-world, after-world, runtime values and all.

The freshness half of case 15 — two PUBLIC calls do not share the table —
is a `#guard` pair: `put_get` mutates and observes within one call;
`fresh_probe` afterwards still sees the empty table (each public call
rebuilds `initWorld`). The differential rows use `put_get`/`fresh_probe`
only in self-contained forms: CPython's imported module PERSISTS across
calls by design, so a cross-call-persistence row would compare different
lifecycles (closed-function semantics, docs/memory-model.md §module
initialization) — that boundary is exactly what `leanpy` module execution
will close.
-/
import Examples.python.sf_tt.proof

open LeanModels LeanModels.Python

load_program sf_tt from "Examples/python/sf_tt/sf_tt.json"

/-! Non-vacuity: concrete runs (values cross-checked against CPython). -/
#py_check sf_tt.put_get(5, 100) = (Val.tuple #[.int 100, .int 110, .int (-60000), .int 2])
#py_check sf_tt.fresh_probe(999) = -60000
#py_check sf_tt.tt_get(1, -1) = -1

/-- The module-init world: the `tt = {}` literal allocated at address 0,
the constant `BIG`, and the resolved globals env. Pinned by `#guard`
below (kernel-computed), stated once here so the theorems can name it. -/
private def w0 : World :=
  ⟨#[.dict #[] 0], [("BIG", .int 60000), ("tt", .ref 0)], []⟩

/-- The world after `tt[1] = 2`: the store bumped the shape version. -/
private def w1 : World :=
  ⟨#[.dict #[(.int 1, .int 2)] 1], [("BIG", .int 60000), ("tt", .ref 0)], []⟩

#guard initWorld sf_tt == w0

/-- **Stateful spec** (case 15, sharing half): a nested `tt_put(1, 2)`
transforms the fresh world into `w1` — the mutation of the module-global
dict is IN the world it hands back. -/
theorem tt_put_callsIn :
    CallsIn sf_tt (initWorld sf_tt) "tt_put" #[.int 1, .int 2] w1 .none := by
  proofs

/-- **Stateful spec** (sharing, read side): from `w1` the next nested call
READS the previous call's mutation — and returns the world untouched. -/
theorem tt_get_callsIn :
    CallsIn sf_tt w1 "tt_get" #[.int 1, .int (-60000)] w1 (.int 2) := by
  proofs

/-- An in-place mutator returning `None` is SPECIFIABLE stateful-ly
(acceptance case 17): `tt_put`'s entire meaning is in the world pair. -/
theorem tt_put_returns_none {w' : World} {v : RVal}
    (h : CallsIn sf_tt (initWorld sf_tt) "tt_put" #[.int 1, .int 2] w' v) :
    v = .none ∧ w' = w1 := by
  proofs

/-! Freshness half of case 15: each PUBLIC call rebuilds the init world —
a `put_get` mutation is invisible to a later public `fresh_probe`/`tt_get`
(there is no world to carry it; `callFunction` is the isolated
observation). -/
#guard callFunction sf_tt "put_get" #[.int 1, .int 7] 4096
  == .ok (.tuple #[.int 7, .int 17, .int (-60000), .int 2])
#guard callFunction sf_tt "tt_get" #[.int 1, .int (-1)] 4096 == .ok (.int (-1))
