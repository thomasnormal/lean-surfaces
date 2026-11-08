// Clean-room R2 wall: a parametric memory with an unsized x/z assignment.
module xz_memory #(parameter int N = 4) (
  input logic clk,
  output logic [31:0] q
);
  logic [31:0] mem [0:N-1];
  assign q = mem[0];
  assign mem[0] = 'bx;
endmodule
