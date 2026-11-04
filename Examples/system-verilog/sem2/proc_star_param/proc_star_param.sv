// SPDX-License-Identifier: Apache-2.0
// WP-PROC E1 in a parametric family: whole-variable assignments are complete at every width (a windowed latch check
// would need a width-fixed target), the temporary sits in the explicit list's scope, and `a[0]` is a select of a
// vector whose width is the parameter.
module proc_star_param #(parameter N = 4) (input [N-1:0] a, b, output reg [N-1:0] y, z);
  always @* begin
    y = 0;
    if (a[0]) y = a & b;
  end
  always @(a or b) z = a + b;
endmodule
