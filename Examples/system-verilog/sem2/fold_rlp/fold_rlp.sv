// Round 4 folds, confirming the round 3 repair (verifier repros vp_lp2,
// vp_lp) with other operators: a typed localparam whose initializer is a
// context-propagating operator over sized literals is evaluated at its
// DECLARED width at each point (IEEE 1800-2023 10.8, 11.8.1). At the default
// N = 2 slang truncates each 4-bit initializer to 2 bits; at N = 8 `~4'd0`
// and `-4'd1` are 255, `4'd8 * 4'd4` is 32 and `(4'd15 + 4'd1) >> 1` is 8.
module fold_rlp #(parameter int N = 2) (
  input  logic [N-1:0] a,
  output logic [N-1:0] o1,
  output logic [N-1:0] o2,
  output logic [N-1:0] o3,
  output logic [N-1:0] o4);
  localparam logic [N-1:0] L1 = ~4'd0;
  localparam logic [N-1:0] L2 = -4'd1;
  localparam logic [N-1:0] L3 = 4'd8 * 4'd4;
  localparam logic [N-1:0] L4 = (4'd15 + 4'd1) >> 1;
  assign o1 = L1 ^ a;
  assign o2 = L2 ^ a;
  assign o3 = L3 ^ a;
  assign o4 = L4 ^ a;
endmodule
