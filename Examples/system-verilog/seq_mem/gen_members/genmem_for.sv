// Downstream clean-room repro: a generate-for memory read family.
module genmem_for #(parameter int N = 4) (
    input logic clk, input logic [31:0] d, output logic [31:0] q
);
  logic [31:0] mem [0:N-1];
  logic [31:0] tap [0:N-1];
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_tap
      assign tap[i] = mem[i];
    end
  endgenerate
  assign q = tap[0];
endmodule
