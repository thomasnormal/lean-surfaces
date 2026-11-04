// ACCEPTED by the clock discipline (WP-Q0, `LeanModels/Sv/ClockGuard2.lean`):
// the N-bit counter with enable and synchronous reset. `clk` is a one-bit
// input port, the only clock, and nothing reads it. The model's one-edge-per-
// cycle semantics is exactly the protocol here (docs/sv-refusals.md,
// `Clock:*`; svgolf/design/sequential/README.md section 4 S0).
module clk_cnt #(parameter int N = 4) (
  input  logic         clk, rst, en,
  output logic [N-1:0] q
);
  always_ff @(posedge clk)
    if (rst) q <= '0;
    else if (en) q <= q + 1'b1;
endmodule
