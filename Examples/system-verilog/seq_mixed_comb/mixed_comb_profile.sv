module mixed_comb_profile(input logic clk, d, output logic q, output logic n);
  always_comb n = d;
  always_ff @(posedge clk) q <= n;
endmodule
