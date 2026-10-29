// Round 4 folds: an INT-class instance override into a typed parameter
// WIDER than 32 bits. slang pushes the parameter's 40 bits into the tree
// (`SignedResize(40, N) * 1024`); the extractor keeps the assignment as a
// root conversion of the parameter's width (`_sym_override_root`). Where
// the 32-bit and the 40-bit products agree every tool agrees; where the
// 32-bit product overflows (N = 2^21, 2^22) the model refuses
// (`Constant:assignment-context`): IEEE 1800-2023 10.8 makes the typed
// override an assignment-like context (40 bits), and the tools split on
// such contexts (docs/sv-oracle-disagreements.md, "Refused where the
// oracles split" (4)).
module fold_rovr_child #(parameter logic signed [39:0] P = 0) (
  input  logic [39:0] a,
  output logic [39:0] o);
  assign o = P ^ a;
endmodule

module fold_rovr #(parameter int N = 5) (
  input  logic [39:0] a,
  output logic [39:0] o);
  fold_rovr_child #(.P(N * 1024)) c (.a(a), .o(o));
endmodule
