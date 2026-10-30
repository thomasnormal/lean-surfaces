/-
Examples/system-verilog/sem2/clk_internal — REFUSED by the clock discipline (`Clock:source`, WP-Q0,
`LeanModels/Sv/ClockGuard2.lean`): the clock is an internal net (a rename of an input).
`load_design_sv2` refuses the envelope at its defaults with the guard's message
(pinned verbatim below); the guard sits BESIDE `name.sem` (the recorded
instantiation lemmas are stated for the unguarded family), so it is run by the
loader, the differential runner (`harness/sv/cases2.json` row `clk_internal`, a
loud-refusal row) and the svGolf checker's probe entry. The model
without the guard ran the design on cycles where no simulator sees an edge
(svgolf/design/sequential/README.md section 4 S0).

  clk_internal.sv      — the SystemVerilog source
  clk_internal.sv.json — generated envelope (extractors/sv/extract.py --top clk_internal)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.clk_internal.agree

/--
error: load_design_sv2: 'Examples/system-verilog/sem2/clk_internal/clk_internal.sv.json' REFUSED — at the defaults, the `always_ff @(posedge ck)` process (writes 'q') is clocked by 'ck', which is not an input port of module 'clk_internal' (it is driven inside the design by a continuous assignment, i.e. a derived, gated or constant-tied signal): the cycle semantics runs every edge process once per cycle and never reads the clock's value (Sem2.cycleStep2), so it is exact only when the clock is an input port of the top module whose edge is the cycle and nothing else uses it; use an input port of the top module as the clock (`Clock:source`, `Design2.clockViolation`)
-/
#guard_msgs (whitespace := lax) in
load_design_sv2 clk_internal from "Examples/system-verilog/sem2/clk_internal/clk_internal.sv.json"

end Examples.«system-verilog».sem2.clk_internal.agree
