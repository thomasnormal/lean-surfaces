// A non-ANSI child INPUT whose separately declared variable has an
// initializer (2026-10-28, round 4 repair, INIT verifier `n_in5`). slang
// keeps the initializer on the internal variable, and the Port dropped it:
// the model read y = b. IEEE 1800-2023 §6.5 counts the initialization as a
// procedural assignment and implies a continuous assignment from the input
// connection, so the design is illegal; slang is silent. Icarus 12.0 and
// Xcelium 24.03 resolve both drivers (y = x1, xx, 0x, x1 for b = 11, 10, 00,
// x1), the Yosys 0.53 netlist keeps 01. Loud (`PortSymbol:initialized-input`).
module pi_in_init_c (a, y);
  input [1:0] a;
  output logic [1:0] y;
  logic [1:0] a = 2'b01;
  assign y = a;
endmodule

module pi_in_init (
  input  logic       clk,
  input  logic [1:0] b,
  output logic [1:0] y
);
  pi_in_init_c u (.a(b), .y(y));
endmodule
