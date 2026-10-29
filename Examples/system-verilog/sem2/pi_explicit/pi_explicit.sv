// A non-ANSI port with an EXPLICIT port expression (`.q(y)`, IEEE 1800-2023
// §23.2.2.1) (2026-10-28, round 4 Lane A). The port `q` is not its internal
// variable `y`, and the symbolic extractor emitted them as two unconnected
// storages: `q` held the initializer (or x) where Icarus 12.0 and Xcelium
// 24.03 read y. Loud (`PortSymbol:explicit-expression`); Verilator 5.042
// and Yosys 0.53 do not parse the form.
module pi_explicit (clk, a, .q(y));
  input clk;
  input a;
  output [1:0] y;
  logic [1:0] y = 2'b10;
  always @(posedge clk) y[0] <= a;
endmodule
