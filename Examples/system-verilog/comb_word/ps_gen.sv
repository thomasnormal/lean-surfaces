// WP-B2 gate 4a: part selects with bounds affine in a genvar (the legacy `PartSel` inside a generate loop).
module ps_gen #(parameter int N = 4) (
  input  logic [4*N-1:0] x,
  output logic [4*N-1:0] y
);
  for (genvar i = 0; i < N; i++) begin : g
    assign y[4*i+3:4*i] = ~x[4*i+3:4*i];
  end
endmodule
