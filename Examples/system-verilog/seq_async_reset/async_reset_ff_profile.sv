module async_reset_ff_profile(input wire clk, rstn, d, output reg q);
  always_ff @(posedge clk or negedge rstn)
    if (!rstn) q <= 1'b0; else q <= d;
endmodule
