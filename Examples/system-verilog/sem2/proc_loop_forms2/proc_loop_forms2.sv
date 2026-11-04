// SPDX-License-Identifier: Apache-2.0
// WP-PROC X1: declared headers master's unroll refused only by the operator name: `>=` with `k--`, `<=` with `m += 1`,
// and a stride-2 loop.
module proc_loop_forms2 (
  input  logic [7:0] a,
  output logic [7:0] y,
  output logic [4:0] s
);
  always_comb begin
    y = '0;
    for (int k = 3; k >= 0; k--) y[k] = a[k] ^ a[7-k];
    for (int m = 0; m <= 3; m += 1) y[7-m] = a[m] & a[7-m];
    s = '0;
    for (int n = 0; n < 8; n = n + 2) s = s + a[n];
  end
endmodule
