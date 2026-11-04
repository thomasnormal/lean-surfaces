// Outside the FF-only profile: a blocking assignment in an always_ff body.
module blocking_ff(input logic clk, input logic [3:0] d, output logic [3:0] q);
  always_ff @(posedge clk) q = d;
endmodule
