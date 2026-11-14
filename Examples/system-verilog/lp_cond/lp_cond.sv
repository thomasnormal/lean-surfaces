// Localparams with comparisons and `?:` (IEEE 1800-2023 §11.4.4, §11.4.5, §11.4.11): a stage count `S` from comparisons
// of the parameter (a 2-state `int`, 0, 1 or 2 stages) and a width `W` with a floor of 4, used as declared widths, generate
// bounds and an index; `Q` (unused) nests a `?:` in an arm and compares by `==` and `!=`. `y` is `a` XORed with `b` once
// per stage; `z` is four copies of `a[0]`.
module lp_cond #(parameter int N = 8) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y,
  output logic [3:0]   z
);
  localparam int S = ((N > 2) ? 1 : 0) + ((N >= 5) ? 1 : 0);
  localparam integer W = (N < 4) ? 4 : N;
  localparam integer Q = (N == 3) ? 0 : ((N != 4) ? 1 : 2);
  logic [S:0][N-1:0] g;
  logic [W-1:0] u;
  genvar i, k;
  generate
    for (i = 0; i < N; i++) begin : g_in
      assign g[0][i] = a[i];
    end
    for (k = 0; k < S; k++) begin : g_st
      for (i = 0; i < N; i++) begin : g_node
        assign g[k+1][i] = g[k][i] ^ b[i];
      end
    end
    for (i = 0; i < N; i++) begin : g_out
      assign y[i] = g[S][i];
    end
    for (i = 0; i < W; i++) begin : g_u
      assign u[i] = a[0];
    end
  endgenerate
  assign z = u[3:0];
endmodule
