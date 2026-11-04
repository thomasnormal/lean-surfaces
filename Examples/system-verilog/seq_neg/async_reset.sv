// Outside the FF-only profile: an asynchronous reset branch (posedge clk or negedge rst_n).
module async_reset(input logic clk, input logic rst_n, input logic [3:0] d, output logic [3:0] q);
  always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) q <= 4'd0;
    else q <= d;
endmodule
