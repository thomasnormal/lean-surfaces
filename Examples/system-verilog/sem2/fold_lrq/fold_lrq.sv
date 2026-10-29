// Round 3 folds, item 4: `$left`/`$right`/`$low` of a signal whose range
// depends on a parameter are outside the tier. slang folds them at the
// DEFAULT point, and the symbolic tree used to carry that literal at every
// point (`$left(v)` of `logic [N-1:0] v` read 2 for every N): now loud
// (`ConversionExpression:default-point-fold`).
module fold_lrq #(parameter int N = 3) (
  input  logic [N-1:0] v,
  output logic [7:0]   o1,
  output logic [7:0]   o2,
  output logic [7:0]   o3
);
  assign o1 = $left(v);
  assign o2 = $right(v);
  assign o3 = $low(v);
endmodule
