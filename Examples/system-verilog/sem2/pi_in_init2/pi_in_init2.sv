// `pi_in_init` with the child input connected through a parent variable
// (2026-10-28, round 4 repair, INIT verifier `n_in6`). Icarus 12.0 gives
// y = b (11, 10, 00, x1), Xcelium 24.03 resolves the initializer with it
// (x1, xx, 0x, x1), the Yosys 0.53 netlist keeps 01: the tools split, and
// the model used to follow Icarus silently. Loud
// (`PortSymbol:initialized-input`).
module pi_in_init2_c (a, y);
  input [1:0] a;
  output logic [1:0] y;
  logic [1:0] a = 2'b01;
  assign y = a;
endmodule

module pi_in_init2 (
  input  logic       clk,
  input  logic [1:0] b,
  output logic [1:0] y
);
  logic [1:0] w;
  assign w = b;
  pi_in_init2_c u (.a(w), .y(y));
endmodule
