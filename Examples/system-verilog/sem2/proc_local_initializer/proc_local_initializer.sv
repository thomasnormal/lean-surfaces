// SPDX-License-Identifier: Apache-2.0
// WP-PROC L1 follow-up: a closed static block-local initializer is hoisted
// with the variable and remains visible to the always_comb body.
module proc_local_initializer (
  input  logic [7:0] a,
  output logic [7:0] y
);
  always_comb begin
    logic [7:0] bias = 8'h5a;
    y = a ^ bias;
  end
endmodule
