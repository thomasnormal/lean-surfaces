// ACCEPTED by the clock discipline (WP-Q0): a serial-in shift register with
// synchronous reset, one input-port clock, never read.
module clk_shreg #(parameter int N = 4) (
  input  logic         clk, rst, d,
  output logic [N-1:0] q
);
  always_ff @(posedge clk)
    if (rst) q <= '0;
    else q <= {q[N-2:0], d};
endmodule
