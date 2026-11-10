// A signed operand is widened to the unsized integer comparison's width.
// IEEE 1800-2023 §§11.4.4 and 11.8.1–11.8.2.
module signed_compare_widen (
  input logic signed [7:0] x,
  output logic y
);
  assign y = x >= 0;
endmodule
