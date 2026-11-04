// SPDX-License-Identifier: Apache-2.0
// Fuel regression: a parameter-bound loop with 200 trips stays structural.
module symbolic_parameter_for_large #(
  parameter int N = 200
) (
  input logic [199:0] a,
  output logic [199:0] y
);
  always_comb begin
    y = '0;
    for (int i = 0; i < N; i++)
      y[i] = a[i];
  end
endmodule
