// WP-B2 gate 4c: the AND mask `a & {N{b[i]}}` of a partial product (the replicated operand is ONE bit select, the
// count a parameter): row `i` of `pp` is `a` when bit `i` of `b` is set and zero otherwise.
module repl_mask #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  output logic [N-1:0][N-1:0] pp
);
  for (genvar i = 0; i < N; i++) begin : g
    assign pp[i] = a & {N{b[i]}};
  end
endmodule
