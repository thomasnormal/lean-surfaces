// A generate bound that is a product of genvars (`j < i * i + 1`): not affine in the parameters and the enclosing genvars.
module gen_sq_bound #(parameter int N = 4) (
  input  logic [N-1:0]        a,
  output logic [N-1:0][4*N-1:0] t
);
  genvar i, j;
  generate
    for (i = 0; i < N; i++) begin : g_row
      for (j = 0; j < i * i + 1; j++) begin : g_col
        assign t[i][j] = a[i];
      end
    end
  endgenerate
endmodule
