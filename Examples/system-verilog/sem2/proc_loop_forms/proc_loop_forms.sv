// SPDX-License-Identifier: Apache-2.0
// WP-PROC X1: Verilog-2001 loop headers: the iterator is a module-level `integer` assigned in the header, shared
// by several loops, with `<=`, `>=`, `+=` and `i--`; the unrolled body binds it per iteration.
module proc_loop_forms (
  input  [7:0] a,
  output reg [7:0] y, z,
  output reg [3:0] c
);
  integer i, j;
  always_comb begin
    y = 8'd0;
    for (i = 0; i < 8; i = i + 1) y[i] = a[7-i];
    z = 8'd0;
    for (j = 0; j <= 7; j += 1) z[j] = a[j] ^ y[j];
    c = 4'd0;
    for (i = 7; i >= 0; i--) c = c + a[i];
  end
endmodule
