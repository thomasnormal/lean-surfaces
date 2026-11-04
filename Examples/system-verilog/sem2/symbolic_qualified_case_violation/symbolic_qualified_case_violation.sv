// SPDX-License-Identifier: Apache-2.0
// Qualified-case violations are loud in the symbolic runner.
module symbolic_qualified_case_violation (
  input logic [1:0] a,
  output logic y
);
  always_comb begin
    y = 1'b0;
    unique case (a)
      2'b01: y = 1'b1;
    endcase
  end
endmodule
