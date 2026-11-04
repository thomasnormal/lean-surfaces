// SPDX-License-Identifier: Apache-2.0
// WP-PROC E1: level-sensitive `always` blocks are always_comb blocks under the rules R1 to R6 (docs/sv-proc-lowering.md):
// an implicit @* with a temporary, an explicit list that names every read, a `case` with a default, a single-event
// list, and a ripple chain through the windows an unrolled loop wrote. Verilog-2001 style (non-ANSI header).
module proc_star (a, b, s, y, z, w, c);
  input [7:0] a, b;
  input [1:0] s;
  output reg [7:0] y, z;
  output reg w;
  output reg [7:0] c;
  integer i;
  reg [7:0] t;
  always @* begin
    t = a ^ b;
    if (s[0]) y = t & a; else y = t | b;
  end
  always @(a or b or s) begin
    case (s)
      2'd0: z = a & b;
      2'd1: z = a | b;
      2'd2: z = a ^ b;
      default: z = ~a;
    endcase
  end
  always @(a) w = ^a;
  always @* begin
    c[0] = a[0] ^ b[0];
    for (i = 0; i < 7; i = i + 1)
      c[i+1] = (c[i] & a[i+1]) | b[i+1];
  end
endmodule
