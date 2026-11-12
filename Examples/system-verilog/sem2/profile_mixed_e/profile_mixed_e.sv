module profile_mixed_e(input logic clk, rst, d, output logic q, output logic y);
  always_ff @(posedge clk or negedge rst)
    if (!rst) q <= 1'b0; else q <= d;
  assign y = q;
endmodule
