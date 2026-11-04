// REFUSED by the clock discipline (`Clock:source`, WP-Q0): an assign-derived
// (gated) clock. Measured on Xcelium 24.03 (svgolf/design/sequential/
// experiments.md E5): the counter counts only the enabled edges, `0 0 1 2 3
// 4`; the model's one-edge-per-cycle semantics would count every cycle.
module clk_gated (
  input  logic       clk, en, rst,
  output logic [3:0] q
);
  logic g;
  assign g = clk & en;
  always_ff @(posedge g)
    if (rst) q <= '0;
    else q <= q + 1'b1;
endmodule
