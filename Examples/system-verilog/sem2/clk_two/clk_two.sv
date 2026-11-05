// Exact multi-clock E witness: each instant names the clocks that rise
// together; coincident edges sample old values before the joint NBA commit.
module clk_two (
  input  logic clk1, clk2, d,
  output logic a, b
);
  always_ff @(posedge clk1) a <= d;
  always_ff @(posedge clk2) b <= a;
endmodule
