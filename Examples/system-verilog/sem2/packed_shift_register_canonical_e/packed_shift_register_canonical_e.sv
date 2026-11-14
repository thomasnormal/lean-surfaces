// Canonical-E clean-room fixture: a parameter-width packed shift register
// uses a part-select and concatenation on an NBA RHS (IEEE 1800-2023 §§7.4,
// 10.4.2, 11.4.12).
module packed_shift_register_canonical_e #(parameter integer N = 4) (
  input logic clk,
  input logic v,
  output logic [N-1:0] q
);
  logic [N-1:0] t;
  always_ff @(posedge clk) t <= {t[N-2:0], v};
  assign q = t;
endmodule
