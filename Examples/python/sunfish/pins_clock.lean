/-
sunfish pin file: the ∀-TRACE transport at search scale — the pass-7
CLOCK-ERASURE payoff (docs/memory-model.md §clock erasure). The
pass-5/6 pins ran at the EMPTY clock trace; `boundProbeT_all_traces`
below transports ANY decided empty-trace probe to EVERY seeded trace
(`ClockTrace.WallClock` — no side condition), composing the
`evalExpr`/`callIn` erasure conjuncts through the probe's projections.

THE MEASURED BOUNDARY (recorded in the §clock erasure as-built notes):
discharging a search-scale empty-trace hypothesis AS A THEOREM needs a
kernel run whose cost is dominated by `initWorld` — one 2-node probe
exceeded 16 minutes of `decide +kernel`, versus ~seconds under the
UNTRUSTED evaluator that `#guard` actually uses (its own docstring:
passing "is *not* a proof"). So this file lands the transport THEOREM
(seconds to check, reusable for every probe) plus NATIVE `#guard` pins
of the seeded surface — the same trust level as the entire existing
pin battery — and the unconditional search-scale `∀ tr` THEOREM waits
on a kernel-affordable concrete-run route (open, backlog).
`clock_lab.pure_sum_all_traces_transported` remains the unconditional
exemplar of the transport at symbolic-execution scale.

Part of the pass-7 SPEC-POLE SPLIT: the program and shared probe defs
come from `pins_common.lean` — after an envelope re-extraction, edit
THAT file; this file rebuilds through the import.

THE BATTERY IS SHARDED (2026-08-25). This file keeps the prose; the
probes live in three leaves that elaborate in PARALLEL.

  `pins_clock_transport`  the ∀-trace transport theorem     (0 guards)
  `pins_clock_probe`      the seeded surface                (5 guards)
  `pins_clock_walk`       the depth-4 stepping walk         (1 guard)

AND THE SHARDING BUYS LESS HERE THAN IT DOES FOR `pins_bound`, which is
worth stating rather than discovering later: this module's cost is
dominated by the SINGLE guard in `_walk` — a 13-step search generator at
fuel 4000000 that crosses node 2048. One certificate cannot be split
without changing it, and splitting the walk in two would re-run the first
twelve steps in both halves, doubling the work rather than halving the
wall. So `_walk` is the critical path, and the win here is that it now
overlaps `pins_bound`'s five leaves instead of queueing behind the rest
of this file.

NO probe dropped, NO fuel changed, every expected value byte-identical.
-/
import Examples.python.sunfish.pins_clock_transport
import Examples.python.sunfish.pins_clock_probe
import Examples.python.sunfish.pins_clock_walk
