// WP-G four-state contract: the conditional EXPRESSION `c ? a : b` is not the procedural `if`: a condition that is x/z MERGES the two arms bit by bit (equal known bits survive, every other bit is x), a condition with a definite 1 bit selects the first arm (so a 2-bit 1x selects it, 0x merges). Scalar and vector arms, a vector condition, a nested ?:, and the same ?: as the right-hand side of a procedural assignment. Pinned against Xcelium 24.03.
module wpg_tern_x (
  input  logic c,
  input  logic [1:0] v,
  input  logic [3:0] a,
  input  logic [3:0] b,
  input  logic d,
  input  logic e,
  output logic t1,
  output logic [3:0] t4,
  output logic [3:0] tv,
  output logic tn,
  output logic [3:0] tp
);
  assign t1 = c ? a[0] : b[0];
  assign t4 = c ? a : b;
  assign tv = v ? a : b;
  assign tn = c ? a[0] : (d ? b[0] : e);
  always_comb begin tp = c ? a : b; end
endmodule
