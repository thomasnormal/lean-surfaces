/-
Examples/system-verilog/sem2/clk_child_ok — ACCEPTED by the clock discipline (WP-Q0,
`LeanModels/Sv/ClockGuard2.lean`): a child register clocked through a bare connection to the parent's input-port clock (the connection assign is a plain copy that nothing reads).
`load_design_sv2` loads it, and the instantiated design (`name.sem`) passes
`Design2.clockViolation` (the loader's check, run at the defaults and at every
probed point) with no loud process. The `harness/sv/cases2.json` row(s) named
`clk_child_ok` run it against Icarus 12 and the pinned Xcelium trace.

  clk_child_ok.sv      — the SystemVerilog source
  clk_child_ok.sv.json — generated envelope (extractors/sv/extract.py --top clk_child_ok)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.clk_child_ok.agree

open LeanModels.Sv

load_design_sv2 clk_child_ok from "Examples/system-verilog/sem2/clk_child_ok/clk_child_ok.sv.json"

#guard clk_child_ok.sem.clockAdmits
#guard !clk_child_ok.sem.hasUnsupported

end Examples.«system-verilog».sem2.clk_child_ok.agree
