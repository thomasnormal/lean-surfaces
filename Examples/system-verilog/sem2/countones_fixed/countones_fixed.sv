// SPDX-License-Identifier: Apache-2.0
// Fixed-width $countones: x/z bits are not counted.
module countones_fixed (
  input  logic [7:0] a,
  output logic [31:0] y
);
  assign y = $countones(a);
endmodule
