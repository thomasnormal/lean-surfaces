// Generate loops whose bound names the genvar of the loop around them (IEEE 1800-2023 §27.4: the bound of a loop
// generate scheme is a constant expression, and an enclosing loop's genvar is a constant inside its block): row `i` of
// `t` is filled by two triangular loops, the cells `j <= i` with an AND term and the cells above the diagonal with a
// zero. `y` is the diagonal.
module gen_tri #(parameter int N = 4) (
  input  logic [N-1:0]        a, b,
  output logic [N-1:0][N-1:0] t,
  output logic [N-1:0]        y
);
  genvar i, j;
  generate
    for (i = 0; i < N; i++) begin : g_row
      for (j = 0; j < i + 1; j++) begin : g_lo
        assign t[i][j] = a[j] & b[i - j];
      end
      for (j = 0; j < N - 1 - i; j++) begin : g_hi
        assign t[i][i + 1 + j] = 1'b0;
      end
      assign y[i] = t[i][i];
    end
  endgenerate
endmodule
