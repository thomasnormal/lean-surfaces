/-
Examples/system-verilog/sem2/clk_fsm — ACCEPTED by the clock discipline (WP-Q0,
`LeanModels/Sv/ClockGuard2.lean`): an enum FSM with combinational outputs.
`load_design_sv2` loads it, and the instantiated design (`name.sem`) passes
`Design2.clockViolation` (the loader's check, run at the defaults and at every
probed point) with no loud process. The `harness/sv/cases2.json` row(s) named
`clk_fsm` run it against Icarus 12 and the pinned Xcelium trace.

  clk_fsm.sv      — the SystemVerilog source
  clk_fsm.sv.json — generated envelope (extractors/sv/extract.py --top clk_fsm)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.clk_fsm.agree

open LeanModels.Sv

load_design_sv2 clk_fsm from "Examples/system-verilog/sem2/clk_fsm/clk_fsm.sv.json"

#guard clk_fsm.sem.clockAdmits
#guard !clk_fsm.sem.hasUnsupported

end Examples.«system-verilog».sem2.clk_fsm.agree
