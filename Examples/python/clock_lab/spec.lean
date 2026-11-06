import LeanModels
import Examples.python.clock_lab.proof

/-!
# clock_lab — the trace-clock acceptance set

Concrete regressions for THE TRACE CLOCK (docs/memory-model.md §the
trace clock, pass 6), pinned two ways: differential rows in
`harness/cases.json` (the CPython side receives a deterministic stub while
the model checks the integer-trace type boundary) and the `#guard`
non-vacuity checks here
(`callFunctionClock` — the clock rows have no `#py_check` surface,
deliberately: `callFunction` is the EMPTY trace).

The claims worth naming, each falsifying a cheaper design:

* **Zero-argument reads are loud.** `read_clock`, `read_twice`, `dead_clock`,
  and `armed` refuse until the explicit trace carries binary64 readings;
  the old integer result would silently change CPython's return type.
* **The arity edge remains faithful.** `time.time(1)` evaluates its
  argument and raises CPython's exact `TypeError` without touching the
  trace.
* **The refusal is fuel-independent.** Empty and nonempty integer traces
  both hit the same type boundary, at two fuels for the armed shape.
* **The admission has edges.** A LOCAL `time` shadows the clock
  (`shadowed` — no pop, with CPython's faithful `AttributeError`);
  `time.time(1)` raises CPython's exact arity `TypeError` after evaluating
  the argument (`call_with_arg`); the trace is not consumed.

`pure_sum` never consults the clock: `pure_sum_all_traces`
(`proof.lean`) is the LAB-SCALE trace-quantified theorem — the result
is identical for ALL traces (`ClockTrace.WallClock`, the unconstrained
class), proved by SYMBOLIC EXECUTION with the trace free (a run that
never pops never scrutinizes it; the measured route note in
`proof.lean` records why not `rfl`).
-/

open LeanModels LeanModels.Python

load_program clock_lab from "Examples/python/clock_lab/clock_lab.json"

/-! ### the census: the clock admission holds on this module (the
benign `import time`, nothing else binding `time`, no `global`), and
`Stop` is an admitted exception class. -/

#guard moduleClockOk clock_lab
#guard clock_lab.classes.map (fun c => (c.name, c.ok, c.isExc)) ==
  #[("Stop", true, true), ("MiniSearcher", true, false)]

/-! ### non-vacuity: the clock-free surface first (`#py_check` — the
empty trace), then the clock rows (`callFunctionClock`). -/

#py_check clock_lab.pure_sum(10) = 55
#py_check clock_lab.pure_sum(0) = 0

/-! ### zero-argument reads refuse until the trace carries binary64 values -/

def clockTypeRefusal : String :=
  "time.time() readings are outside the tier until the clock trace carries binary64 values (CPython returns float)"

#guard callFunctionClock clock_lab "read_clock" #[] [123] 4096 matches
  .unsupported clockTypeRefusal
#guard callFunctionClock clock_lab "read_twice" #[] [5, 9] 4096 matches
  .unsupported clockTypeRefusal
#guard callFunctionClock clock_lab "dead_clock" #[.int 10] [1, 2] 100000 matches
  .unsupported clockTypeRefusal
#guard callFunctionClock clock_lab "armed" #[.int 7, .int 100] [5, 6, 8] 100000 matches
  .unsupported clockTypeRefusal

/-! ### the underrun refusal: loud, message pinned, fuel-independent -/

#guard callFunctionClock clock_lab "read_clock" #[] [] 4096 matches
  .unsupported clockTypeRefusal
#guard callFunctionClock clock_lab "armed" #[.int 7, .int 100] [5] 100000 matches
  .unsupported clockTypeRefusal
#guard callFunctionClock clock_lab "armed" #[.int 7, .int 100] [5] 200000 matches
  .unsupported clockTypeRefusal

/-! ### the admission's edges: shadowing bypasses the clock; args stay faithful -/

#guard callFunctionClock clock_lab "shadowed" #[] [123] 4096 matches
  .exn .attributeError
#py_check clock_lab.call_with_arg() raises
  (.typeError "time.time() takes no arguments (1 given)")

/-! ### the boundary identity: `callFunction` IS the empty trace -/

#guard callFunction clock_lab "pure_sum" #[.int 10] 4096 ==
  callFunctionClock clock_lab "pure_sum" #[.int 10] [] 4096

/-- The LAB-SCALE trace-quantified theorem (the first of its shape —
docs/memory-model.md §the trace clock, axiom classes): a run that never
consults the clock is TRACE-INDEPENDENT. `∀ tr` with no side condition
is exactly the `ClockTrace.WallClock` class: no axioms consumed. The
proof is SYMBOLIC EXECUTION (`proof.lean` — py_simp at concrete fuel;
the measured route note there records why not `rfl`). -/
theorem pure_sum_all_traces (tr : ClockTrace) :
    callFunctionClock clock_lab "pure_sum" #[.int 10] tr 64 =
      .ok (.int 55) := by proofs

/-- The SAME statement by the pass-7 CLOCK-ERASURE transport
(`callFunctionClock_ok`, docs/memory-model.md §clock erasure): the
meta-theorem transports the SINGLE empty-trace instance of the theorem
above to every trace — the `∀ tr` costs nothing beyond the one
empty-trace proof. This is the route the search-sized `∀ tr`
statements take (their empty-trace instances are kernel-discharged —
the as-built section records the measured elaborator/kernel gap and
the `decide +kernel` plan). -/
theorem pure_sum_all_traces_transported (tr : ClockTrace) :
    callFunctionClock clock_lab "pure_sum" #[.int 10] tr 64 =
      .ok (.int 55) := by proofs
