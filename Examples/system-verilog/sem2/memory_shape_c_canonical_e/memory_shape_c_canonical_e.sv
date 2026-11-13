// Parameter-sized unpacked input port and genvar-indexed storage.
module memory_shape_c_canonical_e #(parameter integer W=4, parameter integer N=2) (
  input logic clk, input logic [W-1:0] a [N], output logic [W-1:0] q);
  logic [W-1:0] s [N];
  genvar g;
  generate for (g=0; g<N; g++) begin : gen
    always_ff @(posedge clk) s[g] <= a[g];
  end endgenerate
  assign q = s[0];
endmodule
