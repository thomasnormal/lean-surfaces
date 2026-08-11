import LeanModels
import Examples.python.clock_lab.proof

/-!
# clock_lab — the trace-clock acceptance set

Concrete regressions for THE TRACE CLOCK (docs/memory-model.md §the
trace clock, pass 6), pinned two ways: record-replay differential rows
in `harness/cases.json` (the CPython side of each row binds this
module's `time` name to a stub replaying/recording the SAME integer
trace the model consumes) and the `#guard` non-vacuity checks here
(`callFunctionClock` — the clock rows have no `#py_check` surface,
deliberately: `callFunction` is the EMPTY trace).

The claims worth naming, each falsifying a cheaper design:

* **Readings are inputs, not effects.** `read_clock`/`read_twice` pop
  the trace in order — a frozen-clock or returns-0 stub answers the
  wrong ints; subtraction on readings is exact.
* **The dead-clock regime survives consumption.** `dead_clock` pops
  readings that never bind (`deadline = 1 << 63`, the shipped
  post-#158 regime) — consuming the trace must not disturb the run.
* **The armed deadline stops at the exact reading.** `armed(7, …)`
  under trace `[5, 6, 8]` raises `Stop` at node 12 — the FIRST reading
  `> 7` — composing the clock pop with the pass-4
  raise-through-handler path; CPython stops at the same node.
* **Underrun is a spec error, loudly.** The trace running out refuses
  with the pinned underrun message — never a silent 0, never a timeout
  (fuel-independence pinned by two fuels).
* **The admission has edges.** A LOCAL `time` shadows the clock
  (`shadowed` — no pop, the ordinary loud refusal);
  `time.time(1)` refuses loudly (`call_with_arg` — CPython raises
  `TypeError` AFTER evaluating the arg; the model never fakes it).

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

/-! ### happy pops: readings are inputs, consumed in order -/

#guard callFunctionClock clock_lab "read_clock" #[] [123] 4096 ==
  .ok (.int 123)
#guard callFunctionClock clock_lab "read_twice" #[] [5, 9] 4096 ==
  .ok (.tuple #[.int 5, .int 9, .int 4])

/-! ### the dead clock: consumed, never binding (the shipped regime) -/

#guard callFunctionClock clock_lab "dead_clock" #[.int 10] [1, 2] 100000 ==
  .ok (.tuple #[.int 55, .int 10])

/-! ### the armed deadline: Stop at the exact reading, caught by the
driver's handler (the pass-4 composition) -/

#guard callFunctionClock clock_lab "armed" #[.int 7, .int 100] [5, 6, 8] 100000 ==
  .ok (.tuple #[.int (-1), .int 12])

/-! ### the underrun refusal: loud, message pinned, fuel-independent -/

#guard callFunctionClock clock_lab "read_clock" #[] [] 4096 matches
  .unsupported "clock trace underrun: time.time() has no next reading (the trace is an INPUT — docs/memory-model.md §the trace clock)"
#guard callFunctionClock clock_lab "armed" #[.int 7, .int 100] [5] 100000 matches
  .unsupported "clock trace underrun: time.time() has no next reading (the trace is an INPUT — docs/memory-model.md §the trace clock)"
#guard callFunctionClock clock_lab "armed" #[.int 7, .int 100] [5] 200000 matches
  .unsupported "clock trace underrun: time.time() has no next reading (the trace is an INPUT — docs/memory-model.md §the trace clock)"

/-! ### the admission's edges: shadowing kills the pop; args refuse -/

#guard callFunctionClock clock_lab "shadowed" #[] [123] 4096 matches
  .unsupported _
#guard callFunctionClock clock_lab "call_with_arg" #[] [123] 4096 matches
  .unsupported "time.time() with arguments is outside the trace-clock tier (docs/memory-model.md §the trace clock)"

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
