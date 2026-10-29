// An operand of a compound assignment: `y += t` reads `t` before the block
// writes it. One run per wake-up adds the previous run's `t` (IEEE 1800-2023
// 9.2.2.2.1; Icarus 12 measured). The symbolic extractor refuses the compound
// assignment itself (`AssignmentExpression:compound`), so the body never
// reaches the always_comb self-read guard; lowered to `y = y + t`, the guard
// refuses it (`LeanModels/Sv/CombGuard2.lean` pins that shape).
module rbw_compound (
  input  logic [1:0] a, b,
  output logic [1:0] y
);
  logic [1:0] t;
  always_comb begin
    y = a;
    y += t;
    t = b;
  end
endmodule
