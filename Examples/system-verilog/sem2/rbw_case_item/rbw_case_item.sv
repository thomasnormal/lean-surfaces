// A read in a `case` item (REFUSED): the item expression `t` is compared
// before the block writes `t`. One run per wake-up compares against the
// previous run's `t` (IEEE 1800-2023 9.2.2.2.1). ls-sv refuses the block
// (`AlwaysComb:self-read`, LeanModels/Sv/CombGuard2.lean).
module rbw_case_item (
  input  logic [1:0] s, c,
  input  logic       a, b,
  output logic       y
);
  logic [1:0] t;
  always_comb begin
    case (s)
      t:       y = a;
      default: y = b;
    endcase
    t = c;
  end
endmodule
