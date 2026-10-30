/-
Examples/system-verilog/sem2/clk_child_gated — REFUSED by the clock discipline (`Instance:clock`, WP-Q0,
`LeanModels/Sv/ClockGuard2.lean`): a child instance whose clock port is connected to a gated parent signal.
`load_design_sv2` refuses the envelope at its defaults with the guard's message
(pinned verbatim below); the guard sits BESIDE `name.sem` (the recorded
instantiation lemmas are stated for the unguarded family), so it is run by the
loader, the differential runner (`harness/sv/cases2.json` row `clk_child_gated`, a
loud-refusal row) and the svGolf checker's probe entry. The model
without the guard ran the design on cycles where no simulator sees an edge
(svgolf/design/sequential/README.md section 4 S0).

  clk_child_gated.sv      — the SystemVerilog source
  clk_child_gated.sv.json — generated envelope (extractors/sv/extract.py --top clk_child_gated)
  agree.lean — THIS FILE
-/
import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.clk_child_gated.agree

/--
error: load_design_sv2: 'Examples/system-verilog/sem2/clk_child_gated/clk_child_gated.sv.json' REFUSED — at the defaults, instance 'u': clock port 'clk' is connected to 'g', which is not an input port of the instantiating module (a derived or gated clock is outside the single-clock cycle semantics) (`Instance:clock`, `Design2.clockViolation`)
-/
#guard_msgs (whitespace := lax) in
load_design_sv2 clk_child_gated from "Examples/system-verilog/sem2/clk_child_gated/clk_child_gated.sv.json"

end Examples.«system-verilog».sem2.clk_child_gated.agree
