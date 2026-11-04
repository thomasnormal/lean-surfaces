// ACCEPTED by the clock discipline (WP-Q0): an asynchronous active-low reset
// block. `rst_n` is an input port, read as data inside the block (allowed:
// only the CLOCK may not be read), and is not a clock.
module clk_arst #(parameter int N = 4) (
  input  logic         clk, rst_n, en,
  input  logic [N-1:0] d,
  output logic [N-1:0] q
);
  always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) q <= '0;
    else if (en) q <= d;
endmodule
