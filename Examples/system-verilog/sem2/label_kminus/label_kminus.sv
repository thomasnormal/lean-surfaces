// A constant-base `-:` over a parameter-dependent range that is ASCENDING
// at some points: `[K:0]` with K = W - 2 is `[-1:0]` at W = 1, where
// `t[K -: 2]` selects labels -2..-1 (IEEE 1800-2023 §11.5.1), `{x, t[-1]}`.
// Icarus 12.0 reads it as `t[-1:0]` (declared in
// docs/sv-oracle-disagreements.md, row `label_kminus_w1`).
module label_kminus #(parameter int W = 4) (
  input  logic [1:0] b,
  output logic [1:0] p,
  output logic [1:0] q
);
  localparam int K = W - 2;
  logic [K:0] t;
  always_comb begin
    t = '0;
    t[K] = b[0];
    t[0] = b[1];
  end
  assign p = t[K -: 2];
  assign q = t[K +: 2];
endmodule
