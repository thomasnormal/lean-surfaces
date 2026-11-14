// Generate loops nested three deep (IEEE 1800-2023 §27.4: a generate block may hold further generate constructs), with
// sites at every depth: `t` holds three copies of each `a[j] ^ b[i]`, `d[i][j]` ANDs two of them, `y[i]` reads `d[i][0]`.
// The second family's innermost bounds name both enclosing genvars (`k < i + j + 1`, `k < N + 1 - i - j`): row `2*i + j`
// of `e` is `a[i] ^ b[i]` up to column `i + j` and zero above it. (Each innermost loop runs at least once in the first
// block of its family: the extractor reads a loop's body off that block, `GenerateFor:no-template` otherwise.)
module gen_deep #(parameter int N = 4) (
  input  logic [N-1:0]          a, b,
  output logic [N-1:0][3*N-1:0] t,
  output logic [N-1:0][N-1:0]   d,
  output logic [2*N-1:0][N+1:0] e,
  output logic [N-1:0]          y
);
  genvar i, j, k;
  generate
    for (i = 0; i < N; i++) begin : g_row
      for (j = 0; j < N; j++) begin : g_col
        for (k = 0; k < 3; k++) begin : g_k
          assign t[i][3*j + k] = a[j] ^ b[i];
        end
        assign d[i][j] = t[i][3*j] & t[i][3*j + 2];
      end
      assign y[i] = d[i][0];
    end
    for (i = 0; i < N; i++) begin : h_row
      for (j = 0; j < 2; j++) begin : h_half
        for (k = 0; k < i + j + 1; k++) begin : h_k
          assign e[2*i + j][k] = a[i] ^ b[i];
        end
        for (k = 0; k < N + 1 - i - j; k++) begin : h_z
          assign e[2*i + j][i + j + 1 + k] = 1'b0;
        end
      end
    end
  endgenerate
endmodule
