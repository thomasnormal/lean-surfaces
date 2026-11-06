// Downstream clean-room repro: [0:N-1] memory in a plain edge process without reset.
module memory_cycle_range_plain #(parameter integer W = 8, N = 4) (
    input wire clk, input wire [W-1:0] d,
    output wire [W-1:0] q
);
  reg [W-1:0] cells [0:N-1];
  always @(posedge clk) cells[0] <= d;
  assign q = cells[0];
endmodule
