// An unsized x/z `case` item over a parameter-width subject whose default
// is 32 bits (round 5 repair, Lane A, 2026-10-29; verifier repro `vp9`):
// no conversion at the default, so the item was a 32-bit `Literal` that
// Lean zero-extended. At N = 40 with b = 36 z then 0001 the model gave 2,
// Icarus 12.0 and the Yosys 0.53 netlist 1. Now loud
// (`IntegerLiteral:unsized-xz-parametric`).
module ux_pdep_case #(parameter int N = 32) (
  input  logic clk,
  input  logic [N-1:0] b,
  output logic [7:0] y
);
  always_comb begin
    case (b)
      'hz1:    y = 8'd1;
      default: y = 8'd2;
    endcase
  end
endmodule
