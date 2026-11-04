// WP-B2 gate 4b: a genvar is read as the amount of a shift, an expression over a genvar (`i + 1`) is not (stage 4d).
module neg_shift_gv #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic [N-1:0][N-1:0] y
);
  for (genvar i = 0; i < N; i++) begin : g
    assign y[i] = a << (i + 1);
  end
endmodule
