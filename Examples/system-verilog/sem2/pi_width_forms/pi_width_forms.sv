// Declaration initializers whose literal differs from the declaration in
// width or signedness (2026-10-28, round 4 Lane A): slang wraps them in an
// implicit conversion (`Resize` / `SignedResize`), which Lean's `instDecl`
// used to refuse as a "non-literal initializer". The extractor now lowers
// the conversion exactly (`_sym_decl_init`): zero-extension (w1, w4, w6),
// truncation (w2, w5), sign-extension (w3, and the variable `t` through
// w8), and an x bit zero-extended at a fixed width (w7). Icarus 12.0,
// Xcelium 24.03 (refsim on vip-ng), Verilator 5.042 (x read as 0) and the
// Yosys 0.53 netlist give w1..w8 = 0010 10 1110 0010 0110 0...011 00x1 0001.
module pi_width_forms (
  input  logic        clk,
  input  logic        a,
  output logic [3:0]  w1 = 2'b10,
  output logic [1:0]  w2 = 4'b1110,
  output logic [3:0]  w3 = 2'sb10,
  output logic [3:0]  w4 = 'b10,
  output logic [3:0]  w5 = 22,
  output logic [39:0] w6 = 'h3,
  output logic [3:0]  w7 = 2'bx1,
  output logic [3:0]  w8
);
  logic [3:0] t = 2'sb01;
  always @(posedge clk) begin
    w1[3] <= a;
    w7[2] <= a;
    t[3] <= a;
  end
  assign w8 = t;
endmodule
