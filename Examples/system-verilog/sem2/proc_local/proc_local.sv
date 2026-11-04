// SPDX-License-Identifier: Apache-2.0
// WP-PROC L1: block-local declarations of an always_comb body (named and nested blocks, one shadowing a module
// variable, selects of a local, a local declared in an unrolled loop body) are hoisted to module variables.
module proc_local (
  input  logic [7:0] a, b,
  output logic [7:0] y, z, w
);
  logic [7:0] t;
  assign t = a ^ b;                  // the module variable the block's own `t` shadows
  always_comb begin : blk
    logic [7:0] t;
    logic [3:0] lo, hi;
    t = a & b;
    lo = t[3:0] | b[3:0];
    hi = t[7:4];
    y = {hi ^ lo, lo};
    begin
      logic [7:0] u;
      u = ~t;
      z = u ^ y;
    end
    w = 8'd0;
    for (int i = 0; i < 8; i++) begin
      logic s;
      s = a[i] ^ t[7-i];
      w[i] = s;
    end
  end
endmodule
