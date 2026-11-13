// IEEE 1800-2023 §6.6: an undriven four-state output wire reads z.
module net_z_output_port_canonical_e #(parameter integer N=4) (
  input logic clk, output wire z_out, output logic [31:0] q);
  logic [31:0] mem [0:N-1];
  assign q = mem[0];
endmodule
