/-
Examples/system-verilog/sem2/clk_pipe2 — ACCEPTED by the clock discipline (WP-Q0,
`LeanModels/Sv/ClockGuard2.lean`): a two-stage pipeline.
`load_design_sv2` loads it, and the instantiated design (`name.sem`) passes
`Design2.clockViolation` (the loader's check, run at the defaults and at every
probed point) with no loud process. The `harness/sv/cases2.json` row(s) named
`clk_pipe2` run it against Icarus 12 and the pinned Xcelium trace.

  clk_pipe2.sv      — the SystemVerilog source
  clk_pipe2.sv.json — generated envelope (extractors/sv/extract.py --top clk_pipe2)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.clk_pipe2.agree

open LeanModels.Sv

load_design_sv2 clk_pipe2 from "Examples/system-verilog/sem2/clk_pipe2/clk_pipe2.sv.json"

#guard (clk_pipe2.sem 1).clockAdmits
#guard !(clk_pipe2.sem 1).hasUnsupported
#guard (clk_pipe2.sem 4).clockAdmits
#guard !(clk_pipe2.sem 4).hasUnsupported
#guard (clk_pipe2.sem 8).clockAdmits
#guard !(clk_pipe2.sem 8).hasUnsupported

end Examples.«system-verilog».sem2.clk_pipe2.agree
