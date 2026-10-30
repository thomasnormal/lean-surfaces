/-
Examples/system-verilog/sem2/clk_reg — REFUSED by the clock discipline (`Clock:source`, WP-Q0,
`LeanModels/Sv/ClockGuard2.lean`): a register is used as a clock (divide-by-two).
`load_design_sv2` refuses the envelope at its defaults with the guard's message
(pinned verbatim below); the guard sits BESIDE `name.sem` (the recorded
instantiation lemmas are stated for the unguarded family), so it is run by the
loader, the differential runner (`harness/sv/cases2.json` row `clk_reg`, a
loud-refusal row) and the svGolf checker's probe entry. The model
without the guard ran the design on cycles where no simulator sees an edge
(svgolf/design/sequential/README.md section 4 S0).

  clk_reg.sv      — the SystemVerilog source
  clk_reg.sv.json — generated envelope (extractors/sv/extract.py --top clk_reg)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.clk_reg.agree

/--
error: load_design_sv2: 'Examples/system-verilog/sem2/clk_reg/clk_reg.sv.json' REFUSED — at the defaults, the `always_ff @(posedge div)` process (writes 'q') is clocked by 'div', which is not an input port of module 'clk_reg' (it is a register): the cycle semantics runs every edge process once per cycle and never reads the clock's value (Sem2.cycleStep2), so it is exact only when the clock is an input port of the top module whose edge is the cycle and nothing else uses it; use an input port of the top module as the clock (`Clock:source`, `Design2.clockViolation`)
-/
#guard_msgs (whitespace := lax) in
load_design_sv2 clk_reg from "Examples/system-verilog/sem2/clk_reg/clk_reg.sv.json"

end Examples.«system-verilog».sem2.clk_reg.agree
