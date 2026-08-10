import LeanModels

/-!
# exc_lab — the exceptions acceptance set (checks-only example)

Concrete regressions for the exceptions tier (docs/memory-model.md
§exceptions, BUILT pass 4), pinned two ways: differential rows in
`harness/cases.json` (CPython the oracle) and the `#py_check`/`#guard`
non-vacuity checks here.

The claims worth naming, each falsifying a cheaper design:

* **The retained-state covenant is observable.** `catch_state` mutates
  a list BEFORE the raise and the handler sees the mutation — a
  rollback-on-exception design answers `130`, CPython answers `230`.
* **Class identity, not truthiness.** `wrong_class`/`nested_try` prove
  a non-matching handler PROPAGATES (out of nested tries, out of the
  whole call) — a catch-everything design cannot answer `raises Stop`.
* **An exception through a RESUME closes the generator.**
  `gen_closes_hard(0)` is the differential twin of the gen_lab status
  pin: after the caught raise, `next(g)` must be `StopIteration`
  (a CLOSED frame) — the pre-tier interpreter answered the fake
  "generator already executing" ValueError, pinned and now flipped.
* **The deadline shape works end to end.** `deadline_capstone` raises
  from a RESUMED frame on a node budget and the driver's handler
  catches mid-iteration — `raise`-through-resume-into-handler, the
  exact control path sunfish's `Stop` serves (with `time.time()`
  replaced by the node counter, exactly as the design records).

The refusal battery below (raw `#guard`s + whitelisted rows) pins the
loud frontier — every deviation from the v0 shape refuses with a
reason, never a guess. No `proof.lean`: checks-only, like `gen_lab`.
-/

open LeanModels LeanModels.Python

load_program exc_lab from "Examples/python/exc_lab/exc_lab.json"

/-! ### the ingestion census: the THIRD class kind. `Stop`/`Other` are
admitted exception classes (`isExc`, and `ok` — nothing else about them
is unsupported); `MiniSearcher` is an ordinary class. -/

#guard exc_lab.classes.map (fun c => (c.name, c.ok, c.isExc)) ==
  #[("Stop", true, true), ("Other", true, true), ("MiniSearcher", true, false)]

/-! ### raise/catch and the retained state -/

#py_check exc_lab.catch_ret(1) = 2
#py_check exc_lab.catch_ret(0) = 1
#py_check exc_lab.catch_state(1) = 230
#py_check exc_lab.catch_state(0) = 202

/-! ### class identity: the non-matching handler propagates -/

#py_check exc_lab.wrong_class(0) = 0
#py_check exc_lab.nested_try(0) = 7
#guard callFunction exc_lab "wrong_class" #[.int 1] 4096
  matches .exn (.user _ "Stop")

/-! ### flow through handlers, and the unwinding of nested calls -/

#py_check exc_lab.raise_flows(6) = 3
#py_check exc_lab.raise_flows(2) = 1
#py_check exc_lab.through_call(1) = 99
#py_check exc_lab.through_call(0) = 0

/-! ### the generator CLOSES on an exception through a resume -/

#py_check exc_lab.gen_closes(0) = 1005
#py_check exc_lab.gen_closes(2) = 23
#py_check exc_lab.gen_closes_hard(2) = 3
#py_check exc_lab.gen_closes_hard(0) raises .stopIteration
#py_check exc_lab.for_over_raising(0) = 1001
#py_check exc_lab.for_over_raising(2) = 5
#py_check exc_lab.for_over_raising(5) = 4

/-! ### the deadline capstone: raise-through-resume-into-handler -/

#py_check exc_lab.deadline_capstone(10, 3) = -2996
#py_check exc_lab.deadline_capstone(4, 100) = 6004
#py_check exc_lab.deadline_capstone(10, 0) = 1

/-! ### the wall clock (docs/memory-model.md §wall-clock time — the
recorded abstraction): `time.time()` may appear in code; the
short-circuit keeps it DEAD under `deadline = None` (the shipped
guard's shape, a differential MATCH), and the moment a deadline makes
it live, EVALUATION refuses loudly with the poisoned-import message
naming the clock. -/

#py_check exc_lab.time_dead(5) = 10
#py_check exc_lab.time_dead(0) = 0
#guard callFunction exc_lab "time_live" #[.int 5] 4096
  matches .unsupported "module-level value of 'time' is outside the G1 tier"

/-! ### the refusal battery (raw `#guard`: `unsupported` has no surface
form — deliberate). Every deviation from the v0 shape is loud. -/

#guard callFunction exc_lab "as_binding" #[.int 1] 4096 matches .unsupported _
#guard callFunction exc_lab "finally_clause" #[.int 1] 4096 matches .unsupported _
#guard callFunction exc_lab "else_clause" #[.int 1] 4096 matches .unsupported _
#guard callFunction exc_lab "bare_except" #[.int 1] 4096 matches .unsupported _
#guard callFunction exc_lab "multi_handler" #[.int 1] 4096 matches .unsupported _
#guard callFunction exc_lab "tuple_handler" #[.int 1] 4096 matches .unsupported _
#guard callFunction exc_lab "except_exception" #[.int 1] 4096 matches .unsupported _
#guard callFunction exc_lab "except_builtin" #[.int 1] 4096 matches .unsupported _
#guard callFunction exc_lab "raise_args" #[.int 1] 4096 matches .unsupported _
#guard callFunction exc_lab "raise_bare" #[.int 1] 4096 matches .unsupported _
#guard callFunction exc_lab "raise_value" #[.int 1] 4096 matches .unsupported _
#guard callFunction exc_lab "raise_from" #[.int 1] 4096 matches .unsupported _
#guard callFunction exc_lab "raise_shadowed" #[.int 1] 4096 matches .unsupported _
#guard callFunction exc_lab "exc_as_value" #[.int 1] 4096 matches .unsupported _
#guard callFunction exc_lab "drive_yield_under_try" #[.int 1] 4096 matches .unsupported _
