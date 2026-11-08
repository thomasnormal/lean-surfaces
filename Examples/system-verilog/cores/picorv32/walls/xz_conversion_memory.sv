// Clean-room wall: a parametric x/z conversion drives a memory cell.
module xz_conversion_memory #(parameter int N = 8) (
  input logic clk,
  output logic [N-1:0] q
);
  logic [N-1:0] mem [0:3];
  assign q = mem[0];
  assign mem[0] = 'bx;
endmodule
