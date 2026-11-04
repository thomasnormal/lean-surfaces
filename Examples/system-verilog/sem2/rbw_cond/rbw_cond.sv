// A read in an `if` condition (REFUSED): `t` decides the branch before the
// block writes it. One run per wake-up uses the previous run's `t` (IEEE
// 1800-2023 9.2.2.2.1); the settle semantics uses the new one. ls-sv refuses
// the block (`AlwaysComb:self-read`, LeanModels/Sv/CombGuard2.lean).
module rbw_cond (
  input  logic a, b, c,
  output logic y
);
  logic t;
  always_comb begin
    if (t) y = a;
    else y = b;
    t = c;
  end
endmodule
