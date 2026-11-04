// SPDX-License-Identifier: Apache-2.0
// WP-PROC C1: compound assignment (`op=`) in an always_comb body: whole variable, bit and part selects, a run-time
// index, and inside literal-bounded loops (the clmul accumulate, a popcount).
module proc_compound (
  input  logic [7:0] a, b,
  input  logic [2:0] k,
  output logic [7:0] y, z, w,
  output logic [3:0] c
);
  always_comb begin
    y = a; y ^= b; y += 8'd3; y <<= 1;
    z = a; z[3] ^= b[0]; z[7:6] |= b[7:6]; z[k] ^= 1'b1;
    w = 8'd0;
    for (int i = 0; i < 8; i++)
      if (b[i]) w ^= a << i;
    c = '0;
    for (int i = 0; i < 8; i++)
      c += a[i];
  end
endmodule
