// SPDX-License-Identifier: Apache-2.0
// A literal-bounded procedural loop is unrolled in the symbolic envelope.
module for_unroll (
  input  logic [3:0] a,
  output logic [3:0] y
);
  always_comb begin
    for (int i = 0; i < 4; i++)
      y[i] = a[i];
  end
endmodule
