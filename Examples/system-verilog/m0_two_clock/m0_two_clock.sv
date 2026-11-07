module m0_two_clock (
  input logic clk_a,
  input logic clk_b,
  input logic d,
  output logic qa,
  output logic qb
);
  always_ff @(posedge clk_a) qa <= d;
  always_ff @(posedge clk_b) qb <= d;
endmodule
