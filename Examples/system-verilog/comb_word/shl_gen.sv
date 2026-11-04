// WP-B2 gate 4b: a genvar as the AMOUNT of a shift (a constant of the instance), here in the rows of a two-dimensional
// array: row `i` of `pp` is `aw << i`.
module shl_gen #(parameter int N = 4) (
  input  logic [2*N-1:0] aw,
  output logic [N-1:0][2*N-1:0] pp
);
  for (genvar i = 0; i < N; i++) begin : g
    assign pp[i] = aw << i;
  end
endmodule
