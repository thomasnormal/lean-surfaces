// SPDX-License-Identifier: Apache-2.0
// A parameter-dependent pure loop with a parameter-valued compound step.
module symbolic_parameter_for_parameter_step #(
  parameter int N = 5,
  parameter int S = 2
) (
  input logic [7:0] a,
  output logic [7:0] y
);
  always_comb begin
    y = 8'b0;
    for (int i = 0; i < N; i += S)
      y[i] = a[i];
  end
endmodule
