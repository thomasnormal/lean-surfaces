// Plain literal initializers at a parameter-dependent width (2026-10-28,
// round 4 repair, INIT verifier `w_lit4`). At the default N = 4 the literal
// has the declared width, so slang inserts no width conversion and the
// extractor emitted the 4-bit `Literal`, which `instDecl` stored unchanged
// at every point (y = 1011 at N = 8, z = 1010 where Icarus gives 00001011
// and 11111010). A 0/1 literal is now the `Int` of its value (two's
// complement for a signed one), converted at each point's declared width.
// Icarus 12.0, Xcelium 24.03 and the Yosys 0.53 netlist agree at N = 1, 2,
// 4, 8, 33 (N = 8: y = 00001011, z = 11111010, u = 0...0101, v = 00000110).
module pi_lit_p #(
  parameter int N = 4
) (
  input  logic          clk,
  input  logic          a,
  output logic [N-1:0]  y = 4'b1010,
  output logic [N-1:0]  z = 4'sb1010,
  output logic [N+27:0] u = 'h5,
  output logic [N-1:0]  v
);
  logic [N-1:0] t = 4'sb0110;
  always @(posedge clk) y[0] <= a;
  assign v = t;
endmodule
