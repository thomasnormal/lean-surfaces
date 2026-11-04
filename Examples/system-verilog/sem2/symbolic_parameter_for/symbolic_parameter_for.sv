// SPDX-License-Identifier: Apache-2.0
// The symbolic loop header is retained and expanded at each parameter point.
module symbolic_parameter_for #(
  parameter int N = 2
) (
  input logic [3:0] a,
  output logic [3:0] y
);
  always_comb begin
    y = 4'b0000;
    for (int i = 0; i < N; i++)
      y[i] = a[i];
  end
endmodule
