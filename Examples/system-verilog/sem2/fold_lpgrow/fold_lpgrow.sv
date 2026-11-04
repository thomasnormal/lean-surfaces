// Round 3 repair (verifier repros vp_lp2, vp_lp): a typed localparam or
// parameter default is evaluated at its DECLARED width at each point
// (IEEE 1800-2023 10.8, 11.8.1: the right-hand side at max(target, its own
// width), with its own signedness). At the default N = 4 slang sized each
// initializer to 4 bits; at N = 16 `8'd200 + 8'd100` keeps its carry (300),
// `4'd15 << 2` its high bits (60), `P + 1'b0` (P = -3) is 2^32 - 3 zero-
// extended past 32 bits, `-1` is all ones and `8'sd100` stays 100.
module fold_lpgrow #(parameter int N = 4, parameter int P = -3,
                     parameter logic [N-1:0] Q = 8'd200 + 8'd100) (
  input  logic [N-1:0] a,
  output logic [N-1:0] o1,
  output logic [N-1:0] o2,
  output logic [N-1:0] o3,
  output logic [N-1:0] o4,
  output logic [N-1:0] o5,
  output logic [N-1:0] o6,
  output logic [N-1:0] o7
);
  localparam logic [N-1:0] L1 = 8'd200 + 8'd100;
  localparam logic [N-1:0] L2 = 4'd15 << 2;
  localparam logic [N-1:0] L3 = P + 1'b0;
  localparam logic [N-1:0] L4 = -1;
  localparam logic [N-1:0] L5 = 8'sd100;
  localparam logic [N-1:0] L6 = 300;
  assign o1 = L1 ^ a;
  assign o2 = L2 ^ a;
  assign o3 = L3 ^ a;
  assign o4 = L4 ^ a;
  assign o5 = L5 ^ a;
  assign o6 = L6 ^ a;
  assign o7 = Q ^ a;
endmodule
