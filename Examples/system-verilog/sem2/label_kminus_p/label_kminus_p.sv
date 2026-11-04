// The `-:` half of `label_kminus` that stays admitted (round 6, 2026-10-29): a
// constant-base `-:` over a parameter-dependent DESCENDING range `[K:0]`,
// K = W - 2, at points where it stays in range (W >= 3: labels K and K-1 are
// both inside). IEEE 1800-2023 11.5.1: `t[K -: 2]` selects labels K down to
// K-1. Where it leaves the range (W <= 2, the ascending range `[-1:0]` at W = 1
// included) the select is partly out of range and is the loud-refusal rows
// `label_kminus_w*`: Xcelium 24.03-s004 reads such a select as all x, the LRM
// (and the model, Icarus 12.0 and Yosys 0.53) as x in the out-of-range bits
// only, and Icarus additionally reads the ascending full-width `-:` as the
// whole vector (docs/sv-oracle-disagreements.md, "Ascending full-width minus
// select").
module label_kminus_p #(parameter int W = 4) (
  input  logic [1:0] b,
  output logic [1:0] p
);
  localparam int K = W - 2;
  logic [K:0] t;
  always_comb begin
    t = '0;
    t[K] = b[0];
    t[0] = b[1];
  end
  assign p = t[K -: 2];
endmodule
