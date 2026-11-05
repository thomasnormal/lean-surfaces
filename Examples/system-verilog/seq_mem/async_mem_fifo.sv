module async_mem_fifo #(parameter integer W = 8, N = 4) (
    input wire clk, rstn, input wire [W-1:0] d,
    output wire [W-1:0] q
);
  logic [W-1:0] mem [N];
  always_ff @(posedge clk or negedge rstn)
    if (!rstn) mem[0] <= '0; else mem[0] <= d;
  assign q = mem[0];
endmodule
