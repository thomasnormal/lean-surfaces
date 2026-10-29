// The child twin of `ux_pdep` (round 5 repair, Lane A, 2026-10-29;
// verifier repro `vp4`): a NON-parametric top instantiates a child whose
// own default is W = 32 at W = 40. The child definition is extracted at
// its defaults (no conversion: a 32-bit `Literal`), and Lean zero-extended
// it in the instance: o1 = 8 zeros, 28 x, 0000, where Icarus 12.0 and the
// Yosys 0.53 netlist give 36 x then 0000. No cross-check applies to this
// shape, so `name.sem` was silently wrong. Now loud
// (`IntegerLiteral:unsized-xz-parametric` in the child's `others`).
module ux_pdep_child_c #(parameter int W = 32) (
  input  logic [3:0] a,
  output logic [W-1:0] o1,
  output logic [W-1:0] o2
);
  assign o1 = 'hx0;
  assign o2 = 'bz;
endmodule
module ux_pdep_child (
  input  logic clk,
  input  logic [3:0] a,
  output logic [39:0] y1,
  output logic [39:0] y2
);
  ux_pdep_child_c #(.W(40)) u (.a(a), .o1(y1), .o2(y2));
endmodule
