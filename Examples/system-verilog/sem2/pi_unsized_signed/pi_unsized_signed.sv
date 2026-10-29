// UNSIZED SIGNED BASED literals as declaration and port initializers (round
// 5 Lane A, 2026-10-29; INIT2 verifier repros `sbd`, `p4`, `nf`). The
// tools split: Icarus 12.0 sizes the literal to its digits and sign-extends
// it (t1 = 'sb1 reads 11111111, t2 = 'sh8 11111000, t3 = 'shF forty ones),
// while Xcelium 24.03, Verilator 5.042, the Yosys 0.53 netlist and IEEE
// 1800-2023 §5.7.1 (at least 32 bits, digits zero-padded) give 00000001,
// 00001000 and 0...01111. At 2e8c8b28 the extractor emitted a
// `SignedResize` that `instDecl` refused ("non-literal initializer");
// round 4 emitted the `Int` (the LRM side, silently). Loud again
// (`Initializer:unsized-signed`; every such literal in the sources is also
// `IntegerLiteral:unsized-signed`).
module pi_unsized_signed #(
  parameter int N = 8
) (
  input  logic         clk,
  input  logic         a,
  output logic [7:0]   y1,
  output logic [7:0]   y2,
  output logic [39:0]  y3,
  output logic [N-1:0] y4,
  output logic [7:0]   y5 = 'sh8
);
  logic [7:0]   t1 = 'sb1;
  logic [7:0]   t2 = 'sh8;
  logic [39:0]  t3 = 'shF;
  logic [N-1:0] t4 = 'sb1;
  always @(posedge clk) y5[0] <= a;
  assign y1 = t1;
  assign y2 = t2;
  assign y3 = t3;
  assign y4 = t4;
endmodule
