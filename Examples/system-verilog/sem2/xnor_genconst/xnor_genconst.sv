// LOUD AT INSTANTIATION (WP-L2): `~^` in a generate condition is a constant position, so it is not
// lowered (`BinaryExpression:BinaryXnor`). `load_design_sv2` loads the envelope (the generate
// condition is not part of the defaults cross-check) and `name.sem` is the loud error design
// "generate if: unsupported node 'BinaryExpression:BinaryXnor' in a constant context".
module xnor_genconst #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  for (genvar i = 0; i < N; i++) begin : g
    if ((i ~^ 1) != 0) begin : t
      assign y[i] = a[i];
    end else begin : e
      assign y[i] = ~a[i];
    end
  end
endmodule
