// SPDX-License-Identifier: Apache-2.0
// WP-PROC C1: compound assignment at a parametric width (the lowering never reads the parameter's value).
module proc_compound_param #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y, z
);
  always_comb begin
    y = a; y += b; y -= 1'b1;
    z = a; z[N-1] ^= b[0]; z[0] |= b[N-1];
  end
endmodule
