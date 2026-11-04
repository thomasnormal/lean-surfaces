// Literal labels over `[N-1:0]`: canonical at the default N = 4, the
// ASCENDING 2-bit `[-1:0]` at N = 0 and `[-2:0]` at N = -1. The selects are
// `ArraySel` paths, normalized against the declared range at every point.
module label_n0 #(parameter int N = 4) (
  input  logic [N-1:0] v,
  input  logic [1:0]   b,
  output logic         o1,
  output logic [1:0]   o2,
  output logic         o3,
  output logic [N-1:0] y,
  output logic [N-1:0] z
);
  assign o1 = v[1];
  assign o2 = v[1 +: 2];
  assign o3 = v[0];
  always_comb begin
    y = '0;
    y[1] = b[0];
  end
  always_comb begin
    z = '0;
    z[1 +: 1] = b[1];
  end
endmodule
