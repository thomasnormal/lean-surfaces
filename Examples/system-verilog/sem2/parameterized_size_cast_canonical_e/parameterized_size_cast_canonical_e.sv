// Canonical-E clean-room fixture: a parameter-sized integral cast keeps its
// source-shaped W'(x) operation at each elaborated parameter point
// (IEEE 1800-2023 §§6.24, 11.8.2).
module parameterized_size_cast_canonical_e #(parameter int W = 2) (
  input logic [7:0] x,
  output logic [W-1:0] y
);
  assign y = W'(x);
endmodule
