// Round 7 folds (round 6 FOLDS verifier blocker 1, repro `vw_szc2`): a size
// cast whose size is a parameter, `M'(…)`, inside a localparam initializer.
// slang binds the size away, so the operand has no bound name, and the
// extractor emitted slang's DEFAULT-point fold (M = 8): X1 = -1, X6 = 44 at
// every M, where Icarus 12.0 and the Yosys 0.53 netlist give 255 and 300 at
// M = 16. Refused: ConversionExpression:default-point-fold.
module fold_szc #(parameter int M = 8) (
  input  logic [3:0] a,
  output logic [63:0] o1, o2, o3);
  localparam int X1 = M'(255);
  localparam int X5 = M'(-1);
  localparam int X6 = M'(300);
  assign o1 = X1;
  assign o2 = X5 + a;
  assign o3 = X6;
endmodule
