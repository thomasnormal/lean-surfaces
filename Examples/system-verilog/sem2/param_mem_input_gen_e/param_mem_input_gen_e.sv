module param_mem_input_gen_e #(parameter int W = 8, parameter int N = 2) (
  input logic clk, input logic [W-1:0] a [N], output logic [W-1:0] q);
  logic [W-1:0] s [N];
  genvar g;
  generate for (g = 0; g < N; g++) begin : gen_s
    always_ff @(posedge clk) s[g] <= a[g];
  end endgenerate
  assign q = s[0];
endmodule
