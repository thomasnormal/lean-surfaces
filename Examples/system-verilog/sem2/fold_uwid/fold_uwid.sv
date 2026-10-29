// Round 6 folds (round 5 FOLDS verifier major 3 and minor 4, repros `vs_uw`,
// `vs_uw3`, `vs_upw2`): an UNTYPED localparam built with + - * or **. IEEE
// 1800-2023 6.20.2 types it by its expression (8 bits for `SB + 1'b1` with an
// 8-bit SB: slang, the Yosys 0.53 netlist); Icarus 12.0 gives it the lossless
// width (9 bits), so `(Y + 8'd255) >> 1` into 8 bits is 130 in Icarus and 2
// in Yosys at the default SB = 5, although no value wraps. `Z` is built on
// `Y` across a shift; `P2 = 2 ** SB` wraps only beyond 64 extra bits at
// SB = 100 (Icarus 1, Yosys 0 for `P2 > 5`). Refused at every point:
// Constant:untyped-width.
module fold_uwid #(parameter int N = 8, parameter logic [N-1:0] SB = 8'd5) (
  input  logic [7:0] a,
  output logic [7:0] o1, o3, o5,
  output logic o2, o4, o6);
  localparam Y = SB + 1'b1;
  localparam Z = (Y + 8'd255) >> 1;
  localparam P2 = 2 ** SB;
  assign o1 = (Y + 8'd255) >> 1;
  assign o2 = (Y + 8'd255) < 8'd10;
  assign o3 = (Y + a) >> 1;
  assign o4 = (Y + a) < 8'd10;
  assign o5 = Z;
  assign o6 = P2 > 5;
endmodule
