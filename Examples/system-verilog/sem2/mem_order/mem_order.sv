// Clean-room witness for the memory route's one-pass comb boundary.
// The source order is intentionally downstream before upstream.
module mem_order(input logic [7:0] a, output logic [7:0] y);
  logic [7:0] mem [0:0];
  logic [7:0] b;
  assign y = b;
  assign b = a;
endmodule
