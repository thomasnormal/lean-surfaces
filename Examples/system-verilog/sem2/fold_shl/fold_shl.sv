// Round 7 folds (round 6 FOLDS verifier blocker 3, repro `vw_shl`): untyped
// localparams built with a LEFT shift. Icarus 12.0 widens `<<` by the shift
// amount ($bits(1 << N) is 40 at N = 8, 72 at N = 40, where the value is
// 2^40 and Yosys 0.53 gives 0; $bits(1 << 3) 35, $bits(7 << 1) 33); slang,
// IEEE 1800-2023 6.20.2 and Yosys keep the 32-bit int. Read as concatenation
// parts the tools split at every point. Refused: Constant:untyped-width.
module fold_shl #(parameter int N = 8) (
  input  logic [3:0] a,
  output logic [79:0] o1, o2, o3, o4, o5);
  localparam B = 1 << N;
  localparam C = 1 << 3;
  localparam D = (1 << N) | 1;
  localparam E = (1 << N) / 2;
  localparam F = 7 << 1;
  assign o1 = {a, B};
  assign o2 = {a, C};
  assign o3 = {a, D};
  assign o4 = {a, E};
  assign o5 = {a, F};
endmodule
