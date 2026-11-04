// SPDX-License-Identifier: Apache-2.0
// A Verilog-2001 external iterator remains symbolic when its bound is a
// parameter; the iterator is dead outside the loop and erased at admission.
module symbolic_parameter_for_external #(
  parameter int N = 2
) (
  input logic [7:0] a,
  output logic [7:0] y
);
  integer i;
  always_comb begin
    y = 8'b0;
    for (i = 0; i < N; i = i + 1)
      y[i] = a[i];
  end
endmodule
