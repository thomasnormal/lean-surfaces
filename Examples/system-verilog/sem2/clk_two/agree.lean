/-
Examples/system-verilog/sem2/clk_two — REFUSED by the clock discipline (`Clock:multiple`, WP-Q0,
`LeanModels/Sv/ClockGuard2.lean`): a second clock port.
`load_design_sv2` refuses the envelope at its defaults with the guard's message
(pinned verbatim below); the guard sits BESIDE `name.sem` (the recorded
instantiation lemmas are stated for the unguarded family), so it is run by the
loader, the differential runner (`harness/sv/cases2.json` row `clk_two`, a
loud-refusal row) and the svGolf checker's probe entry. The model
without the guard ran the design on cycles where no simulator sees an edge
(svgolf/design/sequential/README.md section 4 S0).

  clk_two.sv      — the SystemVerilog source
  clk_two.sv.json — generated envelope (extractors/sv/extract.py --top clk_two)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.clk_two.agree

/--
error: load_design_sv2: 'Examples/system-verilog/sem2/clk_two/clk_two.sv.json' REFUSED — at the defaults, module 'clk_two' has 2 clocks ('clk1', 'clk2'): the cycle step ticks every edge process once, i.e. all of its clocks together, which no stimulus of a real simulator is bound to do; independent or interleaved clocks need the clock-domain model of the sequential layer (S5/S6) and are refused until then; use one clock port; the cycle semantics runs every edge process once per cycle and never reads the clock's value (Sem2.cycleStep2), so it is exact only when the clock is an input port of the top module whose edge is the cycle and nothing else uses it (`Clock:multiple`, `Design2.clockViolation`)
-/
#guard_msgs (whitespace := lax) in
load_design_sv2 clk_two from "Examples/system-verilog/sem2/clk_two/clk_two.sv.json"

end Examples.«system-verilog».sem2.clk_two.agree
