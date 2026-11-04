// SPDX-License-Identifier: Apache-2.0
// Qualified case checks retain their metadata while execution stays first-match.
module symbolic_qualified_case (
  input logic [1:0] a,
  output logic [1:0] y,
  output logic [1:0] z,
  output logic [1:0] w
);
  always_comb begin
    y = 2'b00;
    unique case (a)
      2'b00: y = 2'b01;
      default: y = 2'b10;
    endcase
    z = 2'b00;
    unique0 case (a)
      2'b01: z = 2'b01;
    endcase
    w = 2'b00;
    priority case (a)
      2'b10: w = 2'b01;
      default: w = 2'b10;
    endcase
  end
endmodule
