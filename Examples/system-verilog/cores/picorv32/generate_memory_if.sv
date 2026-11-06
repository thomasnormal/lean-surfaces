module genmem_if #(parameter int N = 4) (
  input logic clk,
  input logic [31:0] d,
  output logic [31:0] q
);
  logic [31:0] mem [0:N-1];
  generate
    if (N > 0) begin : g_mem
      assign q = mem[0];
    end
  endgenerate
endmodule
