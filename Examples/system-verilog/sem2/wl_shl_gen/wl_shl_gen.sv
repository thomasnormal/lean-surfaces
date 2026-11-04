// WP-B2 gate 4b pin P21: a GENVAR as the amount of a shift. `pp[i] = aw << i` (the operand as wide as the row), `qq[i] = a << i` (the operand narrower than the row: zero-extended BEFORE the shift, so nothing is lost), `rr[i] = aw >> i`. The amount is an unsized constant of the instance (32 bits); an x/z bit of the operand travels with the shift, bits shifted in are zero.
module wl_shl_gen #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [2*N-1:0] aw,
  output logic [N-1:0][2*N-1:0] pp,
  output logic [N-1:0][2*N-1:0] qq,
  output logic [N-1:0][2*N-1:0] rr
);
  for (genvar i = 0; i < N; i++) begin : g
    assign pp[i] = aw << i;
    assign qq[i] = a << i;
    assign rr[i] = aw >> i;
  end
endmodule
