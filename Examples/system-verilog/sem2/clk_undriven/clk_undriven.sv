// REFUSED by the clock discipline (`Clock:source`, WP-Q0): the clock is an
// internal signal that nothing drives. The model captured `a & b` in every
// cycle; no simulator ever sees an edge on it (y stays x; Yosys drops the
// flip-flop). The undriven-clock exploit of svgolf/design/sequential/README.md.
module clk_undriven (
  input  logic a, b,
  output logic y
);
  logic clk;
  always_ff @(posedge clk) y <= a & b;
endmodule
