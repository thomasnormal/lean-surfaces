// Output-port initializers through the hierarchy (2026-10-28, round 4 Lane
// A): a non-ANSI child (`output reg [1:0] o = 2'b10;`) and a parametric
// ANSI child whose width-converted initializer is evaluated at the child's
// own point (W = 5: o = 00001), both rewritten by a PLAIN `always`.
// Icarus 12.0, Xcelium 24.03 and the Yosys 0.53 netlist agree.
module pi_hier_plain_c (clk, a, o);
  input clk;
  input a;
  output reg [1:0] o = 2'b10;
  always @(posedge clk) o[0] <= a;
endmodule

module pi_hier_plain_w #(
  parameter int W = 3
) (
  input  logic         clk,
  input  logic         a,
  output logic [W-1:0] o = 2'b01
);
  always @(posedge clk) o[W-1] <= a;
endmodule

module pi_hier_plain (
  input  logic       clk,
  input  logic       a,
  output logic [1:0] y,
  output logic [4:0] z
);
  pi_hier_plain_c u (.clk(clk), .a(a), .o(y));
  pi_hier_plain_w #(.W(5)) v (.clk(clk), .a(a), .o(z));
endmodule
