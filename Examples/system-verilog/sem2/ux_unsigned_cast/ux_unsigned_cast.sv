// `$unsigned` of an unsized x/z-top literal WIDENED by its context, in a
// module with one point (round 5 repair, Lane A, 2026-10-29; verifier
// repro `ex3`). Icarus 12.0 zero-extends the self-determined 32-bit value
// (y1 = 8 zeros, 28 z, 0001), as the model did; the Yosys 0.53 netlist
// extends the z (36 z then 0001; y2 36 x then 0000, y3 40 z). The tools
// split: loud (`CallExpression:unsized-xz-cast`). `$signed('hz1)` (sign
// extension of the z top bit) agrees in every tool and stays admitted.
module ux_unsigned_cast (
  input  logic clk,
  input  logic [7:0] a,
  output logic [39:0] y1,
  output logic [39:0] y2,
  output logic [39:0] y3,
  output logic [39:0] y5
);
  assign y1 = $unsigned('hz1);
  assign y2 = $unsigned('hx0);
  always_comb y3 = $unsigned('bz);
  assign y5 = $unsigned('hz1) | a;
endmodule
