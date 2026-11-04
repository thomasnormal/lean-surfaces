// An unsized literal of mixed bits with an x/z high-order bit, at a
// parameter-dependent width (2026-10-28, round 4 repair): `'hz1` is 36 z
// then 0001 at N = 40 and zzzz0001 at N = 8 (Icarus 12.0, Xcelium 24.03 and
// the Yosys 0.53 netlist agree), a width-dependent value no symbolic
// initializer expresses: loud (`Initializer:x-literal-parametric-width`,
// "non-literal initializer").
module pi_uxz_px #(
  parameter int N = 40
) (
  input  logic         clk,
  input  logic         a,
  output logic [N-1:0] y = 'hz1
);
  always @(posedge clk) y[0] <= a;
endmodule
