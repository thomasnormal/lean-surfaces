// Clean-room item-2 witness: an undriven four-state wire is retained as z
// beside a source-shaped memory declaration.
module unpacked_memory_netz #(parameter int N = 4) (
  input logic clk,
  input logic [7:0] d,
  output logic [7:0] q
);
  logic [7:0] mem [0:N-1];
  wire pcpi_mul_wr;
  always_ff @(posedge clk) mem[0] <= d;
  assign q = mem[0];
endmodule
