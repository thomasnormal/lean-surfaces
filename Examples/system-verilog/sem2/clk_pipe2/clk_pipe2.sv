// ACCEPTED by the clock discipline (WP-Q0): a two-stage pipeline, two
// registers on the one input-port clock.
module clk_pipe2 #(parameter int N = 4) (
  input  logic         clk, rst,
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y
);
  logic [N-1:0] s1;
  always_ff @(posedge clk)
    if (rst) begin
      s1 <= '0;
      y  <= '0;
    end else begin
      s1 <= a ^ b;
      y  <= s1;
    end
endmodule
