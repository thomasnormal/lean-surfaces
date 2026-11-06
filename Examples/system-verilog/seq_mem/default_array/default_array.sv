// Downstream clean-room repro: parameter-sized [N] memory in a plain edge process.
module memory_cycle_default_array #(parameter integer W = 8, N = 4) (
    input wire clk, rstn, input wire [W-1:0] d,
    output wire [W-1:0] q
);
  reg [W-1:0] cells [N];
  always @(posedge clk or negedge rstn)
    if (!rstn) cells[0] <= '0; else cells[0] <= d;
  assign q = cells[0];
endmodule
