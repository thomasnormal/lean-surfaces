// Downstream clean-room repro: genvar-indexed writes into parameter memory.
module memory_gen #(parameter integer W = 8, N = 4) (
    input wire clk, input wire [W-1:0] d,
    output wire [W-1:0] q
);
  logic [W-1:0] cells [0:N-1];
  for (genvar i = 0; i < N; i++) begin : g
    always_ff @(posedge clk) cells[i] <= d;
  end
  assign q = cells[0];
endmodule
