// A nested `if` that writes `t` on some paths only (REFUSED): when c is low
// the read of `t` sees the value from before the block, and `t = e` then
// overwrites it. One run per wake-up shows the previous run's e there (IEEE
// 1800-2023 9.2.2.2.1). ls-sv refuses the block (`AlwaysComb:self-read`,
// LeanModels/Sv/CombGuard2.lean).
module rbw_nested (
  input  logic c, d, a, b, e,
  output logic y
);
  logic t;
  always_comb begin
    if (c) begin
      if (d) t = a;
      else t = b;
    end
    y = t;
    t = e;
  end
endmodule
