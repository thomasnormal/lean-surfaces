// Bits, not whole variables (REFUSED): bit 1 of `t` is read before the block
// writes it and written after, on the only path. An event-driven simulator
// runs the block once per wake-up and is never woken by its own write of `t`
// (IEEE 1800-2023 9.2.2.2.1), so `y` shows the PREVIOUS `b`; the settle
// semantics re-runs the block and gives y = b. ls-sv refuses the block
// (`AlwaysComb:self-read`, LeanModels/Sv/CombGuard2.lean).
module rbw_bits (
  input  logic a, b,
  output logic y
);
  logic [1:0] t;
  always_comb begin
    t[0] = a;
    y = t[1];
    t[1] = b;
  end
endmodule
