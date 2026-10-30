/-
Examples/system-verilog/sem2/clk_child_data — REFUSED by the clock discipline (`Clock:data-read`, WP-Q0,
`LeanModels/Sv/ClockGuard2.lean`): a child that reads its own clock port as data (a copy of the parent's clock).
`load_design_sv2` refuses the envelope at its defaults with the guard's message
(pinned verbatim below); the guard sits BESIDE `name.sem` (the recorded
instantiation lemmas are stated for the unguarded family), so it is run by the
loader, the differential runner (`harness/sv/cases2.json` row `clk_child_data`, a
loud-refusal row) and the svGolf checker's probe entry. The model
without the guard ran the design on cycles where no simulator sees an edge
(svgolf/design/sequential/README.md section 4 S0).

  clk_child_data.sv      — the SystemVerilog source
  clk_child_data.sv.json — generated envelope (extractors/sv/extract.py --top clk_child_data)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.clk_child_data.agree

/--
error: load_design_sv2: 'Examples/system-verilog/sem2/clk_child_data/clk_child_data.sv.json' REFUSED — at the defaults, the continuous assignment to 'u.y' reads 'u.ck', a continuous copy of the clock 'clk' as data: a clock may only be the sensitivity of edge processes (and be copied by a plain `assign t = clk`, which is what a bare instance connection is), because the cycle semantics runs every edge process once per cycle and never reads the clock's value (Sem2.cycleStep2), so it is exact only when the clock is an input port of the top module whose edge is the cycle and nothing else uses it; a clock used as data (`clk & en`, `clk ^ a`, `if (clk)`) is a gated or derived clock (`Clock:data-read`, `Design2.clockViolation`)
-/
#guard_msgs (whitespace := lax) in
load_design_sv2 clk_child_data from "Examples/system-verilog/sem2/clk_child_data/clk_child_data.sv.json"

end Examples.«system-verilog».sem2.clk_child_data.agree
