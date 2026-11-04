// SPDX-License-Identifier: Apache-2.0
// A parameter-dependent pure loop with a literal compound step.
module symbolic_parameter_for_compound_step #(
  parameter int N = 5
) (
  input logic [7:0] a,
  output logic [7:0] y
);
  always_comb begin
    y = 8'b0;
    for (int i = 0; i < N; i += 2)
      y[i] = a[i];
  end
endmodule
