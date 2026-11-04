// SPDX-License-Identifier: Apache-2.0
// WP-PROC N1: a Verilog-2001 (non-ANSI) header with typeless input declarations.
module proc_typeless_nonansi (a, b, y);
  parameter N = 4;
  input [N-1:0] a, b;
  output [N-1:0] y;
  reg [N-1:0] y;
  always_comb y = a & ~b;
endmodule
