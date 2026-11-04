// A run-time index read (REFUSED): `t[s]` may read any bit of `t`, every bit
// of which the block writes later. A may-overlap counts as an overlap. One run
// per wake-up reads the previous run's `t` (IEEE 1800-2023 9.2.2.2.1). ls-sv
// refuses the block (`AlwaysComb:self-read`, LeanModels/Sv/CombGuard2.lean).
module rbw_dyn (
  input  logic [3:0] a,
  input  logic [1:0] s,
  output logic       y
);
  logic [3:0] t;
  always_comb begin
    y = t[s];
    t = a;
  end
endmodule
