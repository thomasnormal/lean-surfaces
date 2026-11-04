// SPDX-License-Identifier: Apache-2.0
// WP-PROC L1: block-local variables of a parametric width (their dimensions stay symbolic).
module proc_local_param #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y
);
  always_comb begin
    logic [N-1:0] t, u;
    t = a & ~b;
    u = t ^ b;
    y = u | t;
  end
endmodule
