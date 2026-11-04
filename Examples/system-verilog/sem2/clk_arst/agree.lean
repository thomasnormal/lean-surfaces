/-
Examples/system-verilog/sem2/clk_arst — ACCEPTED by the clock discipline (WP-Q0,
`LeanModels/Sv/ClockGuard2.lean`): an asynchronous active-low reset block (the reset is an input port, read as data inside the block, not a clock).
`load_design_sv2` loads it, and the instantiated design (`name.sem`) passes
`Design2.clockViolation` (the loader's check, run at the defaults and at every
probed point) with no loud process. The `harness/sv/cases2.json` row(s) named
`clk_arst` run it against Icarus 12 and the pinned Xcelium trace.

  clk_arst.sv      — the SystemVerilog source
  clk_arst.sv.json — generated envelope (extractors/sv/extract.py --top clk_arst)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.clk_arst.agree

open LeanModels.Sv

load_design_sv2 clk_arst from "Examples/system-verilog/sem2/clk_arst/clk_arst.sv.json"

#guard (clk_arst.sem 1).clockAdmits
#guard !(clk_arst.sem 1).hasUnsupported
#guard (clk_arst.sem 4).clockAdmits
#guard !(clk_arst.sem 4).hasUnsupported
#guard (clk_arst.sem 16).clockAdmits
#guard !(clk_arst.sem 16).hasUnsupported

end Examples.«system-verilog».sem2.clk_arst.agree
