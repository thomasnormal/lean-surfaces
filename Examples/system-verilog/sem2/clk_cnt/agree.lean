/-
Examples/system-verilog/sem2/clk_cnt — ACCEPTED by the clock discipline (WP-Q0,
`LeanModels/Sv/ClockGuard2.lean`): the N-bit counter with enable and synchronous reset.
`load_design_sv2` loads it, and the instantiated design (`name.sem`) passes
`Design2.clockViolation` (the loader's check, run at the defaults and at every
probed point) with no loud process. The `harness/sv/cases2.json` row(s) named
`clk_cnt` run it against Icarus 12 and the pinned Xcelium trace.

  clk_cnt.sv      — the SystemVerilog source
  clk_cnt.sv.json — generated envelope (extractors/sv/extract.py --top clk_cnt)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.clk_cnt.agree

open LeanModels.Sv

load_design_sv2 clk_cnt from "Examples/system-verilog/sem2/clk_cnt/clk_cnt.sv.json"

#guard (clk_cnt.sem 1).clockAdmits
#guard !(clk_cnt.sem 1).hasUnsupported
#guard (clk_cnt.sem 4).clockAdmits
#guard !(clk_cnt.sem 4).hasUnsupported
#guard (clk_cnt.sem 16).clockAdmits
#guard !(clk_cnt.sem 16).hasUnsupported

end Examples.«system-verilog».sem2.clk_cnt.agree
