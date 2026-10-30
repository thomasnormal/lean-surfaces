// `~^` in a registered and a procedural position (WP-L2): an `always_ff` body (NBA) and an
// `always_comb` body. The clock discipline (WP-Q0) is satisfied: `clk` is the one input-port clock.
module xnor_seq #(parameter int N = 4) (
  input  logic         clk, rst,
  input  logic [N-1:0] a, b,
  output logic [N-1:0] q,
  output logic [N-1:0] m
);
  always_ff @(posedge clk)
    if (rst) q <= '0;
    else q <= q ~^ a;
  always_comb begin
    m = a ^~ b;
  end
endmodule
