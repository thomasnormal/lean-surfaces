// Round 5 folds: the overrides that stay admitted next to `fold_ovrw` — a
// LEAF override into a child parameter of parameter-dependent width (no
// operator, so no context to split on), an INT-class operator into a FIXED
// 40-bit parameter (refused only where its 32-bit value overflows,
// `fold_rovr`), and an INT-class operator into an `int`.
module fold_ovrwl_c #(parameter int W = 40, parameter logic signed [W-1:0] P = 0,
                      parameter logic signed [39:0] Q = 0, parameter int R = 0) (
  output logic [63:0] o, oq, orr);
  assign o = P;
  assign oq = Q;
  assign orr = R;
endmodule
module fold_ovrwl #(parameter int N = 0) (
  input  logic [3:0] a,
  output logic [63:0] o1, o2, o3);
  fold_ovrwl_c #(.W(N + 40), .P(N), .Q(N << 3), .R(N - 1)) u1 (.o(o1), .oq(o2), .orr(o3));
endmodule
