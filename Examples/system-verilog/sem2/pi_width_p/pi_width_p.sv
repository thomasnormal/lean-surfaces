// The parametric twin of `pi_width_forms` (2026-10-28, round 4 Lane A): the
// conversion's own width is the DEFAULT point's (N = 4), so the extractor
// lowers a 0/1 literal to the `Int` of its value, which `instDecl` converts
// at the declared width of each point (`LVec.ofInt`). Icarus 12.0, Xcelium
// 24.03 and the Yosys 0.53 netlist agree at N = 1, 2, 4, 8, 40 (at N = 1:
// y = 0, z = 0, u = 101; at N = 40 z is 38 ones then 10).
module pi_width_p #(
  parameter int N = 4
) (
  input  logic         clk,
  input  logic         a,
  output logic [N-1:0] y = 2'b10,
  output logic [N-1:0] z = 2'sb10,
  output logic [N+1:0] u = 'h5
);
  always @(posedge clk) y[0] <= a;
endmodule
