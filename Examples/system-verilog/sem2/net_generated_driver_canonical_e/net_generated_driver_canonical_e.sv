// IEEE 1800-2023 §23.3.3: a concrete generate branch supplies one full driver.
module net_generated_driver_canonical_e #(parameter integer N=1) (
  input logic clk, output logic [31:0] q, output logic z_out);
  logic [31:0] mem [0:3];
  wire z;
  generate if (N) begin : g assign z = 1'b0; end endgenerate
  assign q = mem[0];
  assign z_out = z;
endmodule
