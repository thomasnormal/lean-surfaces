// SPDX-License-Identifier: Apache-2.0
// The inner loop deliberately shadows the outer iterator. Retain mode keeps
// both headers, while the default path unrolls the literal inner loop.
module symbolic_nested_parameter_for_shadow #(
  parameter int N = 3
) (
  input logic [15:0] a,
  output logic [15:0] y
);
  always_comb begin
    y = 16'b0;
    for (int i = 0; i < N; i++) begin
      for (int i = 0; i < 2; i++)
        y[i] = y[i] ^ a[i];
    end
  end
endmodule
