import LeanModels

/-!
# clock_lab — proofs

The lab-scale trace-quantified theorem, by SYMBOLIC EXECUTION with the
trace FREE: `py_simp` normalizes the whole run — `initWorld` is closed,
the world is concrete-except-clock, and nothing scrutinizes the trace,
so the free variable rides the world as an inert subterm and the public
result (`Run.toPublic` erases the world) does not contain it. `callIn`
and `execWhile` are passed explicitly (full unfolding is safe at the
small concrete fuel — the `tri_neg_total` pattern).

MEASURED ROUTE NOTE (2026-08-11, recorded so nobody retries the cheap
route): the design predicted plain `rfl` — that is FALSIFIED. The
elaborator's free-variable `whnf` does not share work the way closed
kernel evaluation does: `rfl` here timed out beyond 4,000,000
heartbeats on this ten-iteration run (and `py_simp` at fuel 512 blew
1,000,000 on `isDefEq`; fuel 64 proves it in ~20 s). Consequence,
recorded in docs/memory-model.md §the trace clock and the backlog:
search-sized trace-quantified claims on the shipped file wait for the
CLOCK-ERASURE meta-theorem (transport a decided empty-trace run to
every trace), not per-run normalization.
-/

open LeanModels LeanModels.Python

namespace Examples.python.clock_lab.proof

load_program clock_lab from "Examples/python/clock_lab/clock_lab.json"

/- The LAB-SCALE trace-quantified theorem (statement twin in
`spec.lean`): a run that never consults the clock is
TRACE-INDEPENDENT — `∀ tr` with no side condition is exactly the
`ClockTrace.WallClock` class. (A doc comment cannot precede
`set_option … in theorem` — the recorded H5 parse trap.) -/
set_option maxHeartbeats 4000000 in
set_option maxRecDepth 100000 in
theorem pure_sum_all_traces (tr : ClockTrace) :
    callFunctionClock clock_lab "pure_sum" #[.int 10] tr 64 =
      .ok (.int 55) := by
  py_simp [clock_lab, callIn, execWhile]

/- The transport twin (statement in `spec.lean`): the pass-7
CLOCK-ERASURE route — the empty-trace instance of the theorem above
(`pure_sum_all_traces []`, through the `callFunctionClock_nil`
boundary bridge — ClockErase.lean) plus
`callFunctionClock_ok` gives every trace. No per-trace work of any
kind. (The MEASURED elaborator gap, recorded in docs/memory-model.md
§clock erasure as-built: discharging the hypothesis by `by rfl` on the
concrete run instead costs ~2 min of elaborator `whnf` EVEN AT FUEL 64
— elaborator reduction is ~1000× kernel `#guard` evaluation on this
interpreter — so search-scale transports go through kernel-side
`decide +kernel` once `DecidableEq` instances land, never `by rfl`.) -/
theorem pure_sum_all_traces_transported (tr : ClockTrace) :
    callFunctionClock clock_lab "pure_sum" #[.int 10] tr 64 =
      .ok (.int 55) :=
  callFunctionClock_ok
    (by rw [← callFunctionClock_nil]; exact pure_sum_all_traces []) tr

end Examples.python.clock_lab.proof
