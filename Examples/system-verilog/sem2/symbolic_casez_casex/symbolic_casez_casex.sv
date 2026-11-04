// SPDX-License-Identifier: Apache-2.0
// Symbolic four-state wildcard case matching through CaseMatch.
module symbolic_casez_casex (
  input logic [3:0] a,
  output logic [1:0] y,
  output logic [1:0] z
);
  always_comb begin
    y = 2'b00;
    casez (a)
      4'b1???: y = 2'b01;
      4'b01??: y = 2'b10;
      default: y = 2'b00;
    endcase
    z = 2'b00;
    casex (a)
      4'b1x0x: z = 2'b01;
      4'b00xx: z = 2'b10;
      default: z = 2'b00;
    endcase
  end
endmodule
