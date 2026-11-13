// Clean-room canonical-E row: blocking state updates before edge NBAs.
module memory_edge_blocking_canonical_e #(parameter integer W = 4, parameter integer D = 2) (
  input logic clk, input logic [W-1:0] d,
  output logic [W-1:0] mem0, output logic [W-1:0] mem1,
  output logic [W-1:0] delayed, output logic [W-1:0] marker);
  logic [W-1:0] mem [0:D-1];
  initial begin
    mem[0] = 4'h1;
    mem[1] = 4'h2;
    delayed = '0;
    marker = '0;
  end
  assign mem0 = mem[0];
  assign mem1 = mem[1];
  always @(posedge clk) begin
    marker = d;
    mem[0] = marker;
    delayed <= marker;
    mem[1] <= mem[0];
    marker = '0;
  end
endmodule
