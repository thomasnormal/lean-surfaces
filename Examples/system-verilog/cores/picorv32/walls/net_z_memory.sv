// Clean-room R2 wall: a plain undriven net beside a memory declaration.
module net_z_memory #(parameter int N = 4) (
  input logic clk,
  output logic [31:0] q
);
  logic [31:0] mem [0:N-1];
  wire pcpi_mul_wr;
  assign q = mem[0];
endmodule
