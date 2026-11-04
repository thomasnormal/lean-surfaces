// SPDX-License-Identifier: Apache-2.0
// WP-PROC N2 in a parametric family: a declaration assignment and a whole-net assign at every width (the driver is
// the whole net by its source text, so the decision holds at every point), an `output wire`, an implicit-type output.
module proc_net_param #(parameter N = 4) (input [N-1:0] a, b, output [N-1:0] y, output wire [N-1:0] z);
  wire [N-1:0] t = a & b;
  wire [N-1:0] u;
  assign u = a | b;
  assign y = t ^ u;
  assign z = t + u;
endmodule
