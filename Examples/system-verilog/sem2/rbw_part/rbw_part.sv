// Part-selects (REFUSED): bits [3:2] of `t` are read before the block writes
// them and written after; bits [1:0] are written first, which does not help.
// One run per wake-up reads the previous run's t[3:2] (IEEE 1800-2023
// 9.2.2.2.1). ls-sv refuses the block (`AlwaysComb:self-read`,
// LeanModels/Sv/CombGuard2.lean).
module rbw_part (
  input  logic [1:0] a, b,
  output logic [1:0] y
);
  logic [3:0] t;
  always_comb begin
    t[1:0] = a;
    y = t[3:2];
    t[3:2] = b;
  end
endmodule
