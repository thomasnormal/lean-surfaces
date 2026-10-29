// Round 6 folds (round 5 FOLDS verifier blocker 1, repro `vs_sqn`): a
// 2-state constant target NARROWER than its initializer at the default
// point. slang's tree is `Resize(target, Squash2(default width, op))`; at a
// point where the operand is narrower than the target, the target is the
// context (IEEE 1800-2023 10.8, 11.8.1), so `(U + 1'b1) >> 1` keeps its
// carry: 8 at N = 4 with U = 15 in Icarus 12.0, the Yosys 0.53 netlist and
// slang's elaboration. Also a 2-state target WIDER than its initializer at
// the default (`W40`), whose tree carries the default point's widening.
module fold_sqn #(parameter int N = 32, parameter logic [N-1:0] U = -1,
                  parameter byte PY = (U + 1'b1) >> 1,
                  parameter int K = 40, parameter logic [K-1:0] UK = -1) (
  input  logic [3:0] a,
  output logic [63:0] o1, o2, o3, o4, o5, o6, o7, o8, o9);
  localparam shortint H1 = (U + 1'b1) >> 1;
  localparam byte Y1 = U + 1'b1;
  localparam bit [7:0] B8 = (U + 1'b1) >> 1;
  localparam bit signed [7:0] S8 = (U + 1'b1) >> 1;
  localparam logic [7:0] L8 = (U + 1'b1) >> 1;
  localparam int KI = (UK + 1'b1) >> 1;
  localparam bit [39:0] W40 = (U + 1'b1) >> 1;
  localparam longint LL = (UK + 1'b1) >> 1;
  assign o1 = H1;
  assign o2 = Y1;
  assign o3 = B8;
  assign o4 = S8;
  assign o5 = L8;
  assign o6 = KI;
  assign o7 = PY;
  assign o8 = W40;
  assign o9 = LL;
endmodule
