/-
Examples/system-verilog/sem2/clk_shreg — ACCEPTED by the clock discipline (WP-Q0,
`LeanModels/Sv/ClockGuard2.lean`): a serial-in shift register with synchronous reset.
`load_design_sv2` loads it, and the instantiated design (`name.sem`) passes
`Design2.clockViolation` (the loader's check, run at the defaults and at every
probed point) with no loud process. The `harness/sv/cases2.json` row(s) named
`clk_shreg` run it against Icarus 12 and the pinned Xcelium trace.

  clk_shreg.sv      — the SystemVerilog source
  clk_shreg.sv.json — generated envelope (extractors/sv/extract.py --top clk_shreg)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.clk_shreg.agree

open LeanModels.Sv

load_design_sv2 clk_shreg from "Examples/system-verilog/sem2/clk_shreg/clk_shreg.sv.json"

#guard (clk_shreg.sem 2).clockAdmits
#guard !(clk_shreg.sem 2).hasUnsupported
#guard (clk_shreg.sem 4).clockAdmits
#guard !(clk_shreg.sem 4).hasUnsupported
#guard (clk_shreg.sem 16).clockAdmits
#guard !(clk_shreg.sem 16).hasUnsupported

end Examples.«system-verilog».sem2.clk_shreg.agree
