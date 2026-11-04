// An operand of a compound assignment: `y += t` reads `t` before the block
// writes it. One run per wake-up adds the previous run's `t` (IEEE 1800-2023
// 9.2.2.2.1; Icarus 12 measured). Since WP-PROC C1 (2026-11-01) the symbolic
// extractor lowers the compound assignment to `y = y + t`, and the always_comb
// self-read guard refuses it (`LeanModels/Sv/CombGuard2.lean` pins that shape);
// before C1 it was refused earlier, as `AssignmentExpression:compound`.
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
