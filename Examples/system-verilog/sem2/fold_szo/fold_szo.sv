// Round 7 folds (round 6 FOLDS verifier blocker 1, repro `vw_szo`): the
// override form of `fold_szc`. `.W(M'(255))` and `.W(M'(300) + 1)` into an
// `int W` were slang's default-point folds (-1 and 45 at M = 8) at every M;
// Icarus 12.0 and the Yosys 0.53 netlist give 255 and 301 at M = 16.
// Refused: ConversionExpression:default-point-fold.
module fold_szo_c #(parameter int W = 0) (
  input  logic [3:0] a,
  output logic [63:0] o);
  assign o = W + a;
endmodule
module fold_szo #(parameter int M = 8) (
  input  logic [3:0] a,
  output logic [63:0] o1, o2);
  fold_szo_c #(.W(M'(255))) u1 (.a(a), .o(o1));
  fold_szo_c #(.W(M'(300) + 1)) u2 (.a(a), .o(o2));
endmodule
