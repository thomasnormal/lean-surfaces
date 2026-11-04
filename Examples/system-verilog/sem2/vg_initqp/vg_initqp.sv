// The parametric twin of `vg_initq` (2026-10-28, round 3 CX repair): an
// N-bit output variable port initialized to all ones, bit 0 written by
// always_ff. Since round 4 (Lane A) the always_ff block is REFUSED at every
// N (`ProceduralBlockSymbol:initialized-variable`: Xcelium 24.03
// `*E,MULAXX`, the other tools run it); `pi_width_p` pins a parametric
// initializer with a plain `always` writer.
module vg_initqp #(
  parameter int N = 2
) (
  input  logic clk,
  input  logic a,
  output logic [N-1:0] y = '1
);
  always_ff @(posedge clk) y[0] <= a;
endmodule
