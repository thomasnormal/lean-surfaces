// Clean-room item-2 witness: source-shaped unpacked memory with a
// sequential write and a combinational dynamic read.
module unpacked_memory_comb #(parameter int N = 4) (
  input logic clk,
  input logic we,
  input logic [$clog2(N)-1:0] widx,
  input logic [$clog2(N)-1:0] ridx,
  input logic [7:0] d,
  output logic [7:0] q
);
  logic [7:0] mem [0:N-1];
  always_ff @(posedge clk)
    if (we) mem[widx] <= d;
  always_comb begin
    q = mem[ridx];
  end
endmodule
