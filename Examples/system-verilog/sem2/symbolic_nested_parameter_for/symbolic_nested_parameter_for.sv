// SPDX-License-Identifier: Apache-2.0
// Nested parameter-bound loops retain both headers. The inner bound is the
// outer iterator, so Param2 derives the inner trip list per outer trip.
module symbolic_nested_parameter_for #(
  parameter int N = 4
) (
  input logic [15:0] a,
  output logic [15:0] y
);
  always_comb begin
    y = 16'b0;
    for (int i = 0; i < N; i++)
      for (int j = 0; j < i; j++)
        y[i] = y[i] ^ a[j];
  end
endmodule
