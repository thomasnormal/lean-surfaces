// SPDX-License-Identifier: Apache-2.0
// Parameter-bound header forms: inclusive bound, descending loop, and += c.
module symbolic_parameter_for_header_shapes #(
  parameter int N = 5
) (
  input logic [7:0] a,
  output logic [7:0] y
);
  always_comb begin
    y = 8'b0;
    for (int i = 0; i <= N - 1; i += 1)
      y[i] = a[i];
    for (int j = N - 1; j >= 0; j -= 1)
      y[j] = y[j] ^ a[j];
    for (int k = 0; k < N; k += 2)
      y[k] = y[k] ^ a[k];
  end
endmodule
