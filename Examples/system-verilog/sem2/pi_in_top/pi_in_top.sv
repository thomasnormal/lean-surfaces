// A TOP-level non-ANSI input whose separately declared variable has an
// initializer (2026-10-28, round 4 repair). The testbench drives `a`;
// Icarus 12.0 gives y = a (11, 10, 00, x1), Xcelium 24.03 resolves the
// initializer with it (x1, xx, 0x, x1), the Yosys 0.53 netlist keeps 01.
// Loud (`PortSymbol:initialized-input`).
module pi_in_top (clk, a, y);
  input clk;
  input [1:0] a;
  output logic [1:0] y;
  logic [1:0] a = 2'b01;
  assign y = a;
endmodule
