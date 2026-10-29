// All-x/z unsized literals (`'bx`, `'bz`) in a parametric family with a
// default N = 8 (round 5 repair, Lane A, 2026-10-29; probe
// `gaps5/init2/d/ov2.sv`): slang folds each to an 8-bit `Literal`, which
// Lean zero-extended at every wider point — at N = 16, y2 = 8 zeros then 8
// z, where Icarus 12.0 and the Yosys 0.53 netlist give 16 z (FAIL against
// Icarus at N = 15, 16, 31, 32, 33, 63, 64, 65; PASS at N <= 8). Now loud
// (`IntegerLiteral:unsized-xz-parametric`), although `Fill` would be exact
// for this shape (a recorded over-refusal of the class refusal).
module ux_pdep_fill #(parameter int N = 8) (
  input  logic clk,
  input  logic [1:0] s,
  output logic [N-1:0] y1,
  output logic [N-1:0] y2
);
  assign y2 = 'bz;
  always_comb begin
    case (s)
      2'd0:    y1 = '0;
      2'd1:    y1 = '1;
      default: y1 = 'bx;
    endcase
  end
endmodule
