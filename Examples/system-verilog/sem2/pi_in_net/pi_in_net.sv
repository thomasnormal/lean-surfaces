// A non-ANSI child input whose separately declared NET has a declaration
// assignment (`wire [1:0] a = 2'b01;`, a second continuous driver;
// 2026-10-28, round 4 repair). Icarus 12.0 and Xcelium 24.03 resolve both
// drivers (y = x1, xx, 0x, x1 for b = 11, 10, 00, x1), the Yosys 0.53
// netlist keeps 01; the model read y = b. Loud
// (`PortSymbol:initialized-input`).
module pi_in_net_c (a, y);
  input [1:0] a;
  output logic [1:0] y;
  wire [1:0] a = 2'b01;
  assign y = a;
endmodule

module pi_in_net (
  input  logic       clk,
  input  logic [1:0] b,
  output logic [1:0] y
);
  pi_in_net_c u (.a(b), .y(y));
endmodule
