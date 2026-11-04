// `$bits` of an EXPRESSION in a select label: not a declared signal's width,
// so not carried per point. Refused: `RangeSelectExpression:query-label`.
module bits_expr_label #(parameter int N = 3) (
  input  logic [N-1:0] a,
  input  logic [31:0]  v,
  output logic [1:0]   o1,
  output logic [1:0]   o2
);
  assign o1 = v[$bits(a[1:0]) +: 2];
  assign o2 = v[$bits(a + 1'b1) +: 2];
endmodule
