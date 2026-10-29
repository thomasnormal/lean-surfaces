// Literal labels against parameter-dependent ranges and widths. The legacy
// encoding folded both selects at the DEFAULT parameters (`x[4 +: N]` to
// `[5:4]`, `u[5]` to offset 1), which is wrong at every other parameter
// point; `ArraySel` keeps the labels and normalizes per instance.
module array_param_labels #(parameter int N = 2, parameter int L = 4) (
  input  logic [7:0]   x,
  input  logic [7:L]   u,
  output logic [N-1:0] y,
  output logic         v,
  output logic [1:0]   w
);
  assign y = x[4 +: N];
  assign v = u[5];
  assign w = u[L+1 -: 2];
endmodule
