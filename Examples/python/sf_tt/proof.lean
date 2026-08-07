/-
Proof module for `Examples/python/sf_tt/spec.lean` (three-file example
layout). The two `CallsIn` witnesses are kernel-evaluated concrete runs
(`⟨4096, by rfl⟩` — the `CallsTo.intro` analog at the stateful judgment);
`tt_put_returns_none` pins ANY decided outcome to them through
`CallsIn.functional` (fuel monotonicity at the `callIn` conjunct).
-/
import LeanModels

namespace Examples.python.sf_tt.proof

open LeanModels LeanModels.Python

load_program sf_tt from "Examples/python/sf_tt/sf_tt.json"

private def w0 : World :=
  ⟨#[.dict #[] 0], [("BIG", .int 60000), ("tt", .ref 0)], []⟩

private def w1 : World :=
  ⟨#[.dict #[(.int 1, .int 2)] 1], [("BIG", .int 60000), ("tt", .ref 0)], []⟩

theorem tt_put_callsIn :
    CallsIn sf_tt (initWorld sf_tt) "tt_put" #[.int 1, .int 2] w1 .none :=
  ⟨4096, by rfl⟩

theorem tt_get_callsIn :
    CallsIn sf_tt w1 "tt_get" #[.int 1, .int (-60000)] w1 (.int 2) :=
  ⟨4096, by rfl⟩

theorem tt_put_returns_none {w' : World} {v : RVal}
    (h : CallsIn sf_tt (initWorld sf_tt) "tt_put" #[.int 1, .int 2] w' v) :
    v = .none ∧ w' = w1 := by
  have hf := CallsIn.functional h tt_put_callsIn
  exact ⟨hf.2, hf.1⟩

end Examples.python.sf_tt.proof
