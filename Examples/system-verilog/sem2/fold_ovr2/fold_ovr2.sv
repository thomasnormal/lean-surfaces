// Round 3 repair: instance parameter overrides the tools read alike. A typed
// override that is a leaf, a select or a comparison (`U`, `U[3:0]`,
// `U > V`) and an INT-class one (`N + 2`) are admitted; the child's
// parameter type converts them (`P` keeps U's bits at every N, `R` is
// `N + 2`). The typed `U + V` is the refused shape (row `fold_ovr`).
module fold_ovr2_child #(parameter logic [15:0] P = 0, parameter logic [3:0] S = 0,
                         parameter logic C = 0, parameter int R = 0) (
  input  logic [15:0] a,
  output logic [15:0] o1,
  output logic [15:0] o2
);
  assign o1 = P ^ a;
  assign o2 = {S, C, R[10:0]} ^ a;
endmodule

module fold_ovr2 #(parameter int N = 16) (
  input  logic [15:0] a,
  output logic [15:0] o1,
  output logic [15:0] o2
);
  localparam logic [N-1:0] U = 16'hFFFF;
  localparam logic [7:0] V = 8'd1;
  fold_ovr2_child #(.P(U), .S(U[3:0]), .C(U > V), .R(N + 2)) c (.a(a), .o1(o1), .o2(o2));
endmodule
