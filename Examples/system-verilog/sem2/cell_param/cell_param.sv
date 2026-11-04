// A fixed unpacked array written at an overridable-PARAMETER index
// (2026-10-28, WP2 repair; verifier row `uarr_k`): slang folds `m[K]` at
// the default K = 0, so every K wrote `m[0]` (at K = 1, a = 1 Icarus 12.0
// gives y = zz1z — `m[1]` driven, the other cells undriven — while the
// model drove `m[0]`).
// Refused: `ElementSelect:default-point-index`.
module cell_param #(
  parameter int K = 0
) (
  input  logic       a,
  output logic [3:0] y
);
  logic m [4];
  assign m[K] = a;
  assign y = {m[3], m[2], m[1], m[0]};
endmodule
