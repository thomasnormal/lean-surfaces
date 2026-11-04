// SPDX-License-Identifier: Apache-2.0
// WP-PROC X1: a block-local `integer` iterator assigned in the header (its declaration is dead after the unroll).
module proc_loop_forms_local (
  input  logic [7:0] a,
  output logic [7:0] y
);
  always_comb begin : blk
    integer q;
    y = 8'd0;
    for (q = 0; q < 8; q = q + 1) y[q] = a[q] ^ a[(q + 1) % 8];
  end
endmodule
