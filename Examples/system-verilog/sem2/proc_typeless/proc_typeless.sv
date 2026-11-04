// SPDX-License-Identifier: Apache-2.0
// WP-PROC N1: implicit-type (typeless) ANSI input ports keep their dimensions (`input [N-1:0] a`).
module proc_typeless #(parameter int N = 4) (
  input [N-1:0] a, b,
  input c,
  output logic [N-1:0] y,
  output logic z
);
  assign y = c ? a : b;
  assign z = ^(a & b);
endmodule
