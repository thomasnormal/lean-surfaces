// The `+:` half of `label_kminus` that stays admitted (round 6, 2026-10-29):
// at W = 1 the localparam K = W - 2 is -1 and `t` is the ASCENDING range
// `[-1:0]`, where `t[K +: 2]` selects labels -1 and 0 (IEEE 1800-2023 11.5.1:
// `+:` counts up from the base), both inside. The model, Icarus 12.0, Yosys
// 0.53 and Xcelium 24.03-s004 all agree on it. The `-:` select of the same
// range (`p = t[K -: 2]`, labels -2..-1, partly outside) is the loud-refusal
// row `label_kminus_w1`: the tools split on it (docs/sv-xcelium-audit.md, P1
// and DX1).
module label_kminus_q #(parameter int W = 1) (
  input  logic [1:0] b,
  output logic [1:0] q
);
  localparam int K = W - 2;
  logic [K:0] t;
  always_comb begin
    t = '0;
    t[K] = b[0];
    t[0] = b[1];
  end
  assign q = t[K +: 2];
endmodule
