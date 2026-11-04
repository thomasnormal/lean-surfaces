// `$high` of a declared signal as a label: refused (`RangeSelectExpression:
// query-label`): the constant tier reads it as `width - 1`, exact only for a
// `[W-1:0]` range at every point (here `[N:1]`).
module high_label #(parameter int N = 6) (
  input  logic [N:1] a,
  input  logic [7:0] v,
  output logic [1:0] o
);
  assign o = v[$high(a) -: 2];
endmodule
