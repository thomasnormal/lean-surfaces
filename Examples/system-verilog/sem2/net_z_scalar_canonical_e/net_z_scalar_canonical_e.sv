// IEEE 1800-2023 §6.6: an undriven four-state wire reads z.
module net_z_scalar_canonical_e #(parameter integer N=4) (
  input logic clk, output logic [31:0] q, output logic z_out);
  logic [31:0] mem [0:N-1];
  wire z;
  assign q = mem[0];
  assign z_out = z;
endmodule
