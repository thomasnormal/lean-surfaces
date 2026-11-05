module async_reset_comb_profile(input logic clk, rstn, d, output logic q, output logic n);
  assign n = d;
  always_ff @(posedge clk or negedge rstn)
    if (!rstn) q <= 1'b0; else q <= n;
endmodule
