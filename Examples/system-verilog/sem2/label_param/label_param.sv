// Parameter (static, non-literal) labels over a parameter-dependent range:
// `ArraySel` paths, normalized against `[N-1:0]` at every point (out of range,
// or the ascending `[-1:0]` when N <= 0).
module label_param #(parameter int N = 4, parameter int P = 1) (
  input  logic [N-1:0] v,
  input  logic [1:0]   b,
  output logic         o,
  output logic [1:0]   o2,
  output logic [N-1:0] y
);
  assign o  = v[P];
  assign o2 = v[P +: 2];
  always_comb begin
    y = '0;
    y[P] = b[0];
    y[P-1 -: 1] = b[1];
  end
endmodule
