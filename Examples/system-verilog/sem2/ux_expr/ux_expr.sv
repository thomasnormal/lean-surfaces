// Unsized literals whose high-order bit is x or z, WIDENED by an expression
// context in a module with one parameter point (2026-10-28, round 4 repair,
// INIT verifier `w_uxa`). IEEE 1800-2023 §5.7.1 extends them with that bit;
// the symbolic `Resize` zero-extended them (y read 8 zeros then 32 x). The
// extractor now pads them to the context width
// (`_sym_unsized_xz_widening`). Icarus 12.0 and Xcelium 24.03 give y = 40 x,
// z = 36 z then 0001 at a = 1, and d = b | 36 x then 0000; Yosys 0.53 reads
// the same constants (`prep`: 40'hzzzzzzzzz1, 36'hxxxxxxxxx); its
// synthesized netlist reads x and z as don't-cares (z = 0...0001, d = b's
// high bits set), the synthesis reading of every x/z constant.
module ux_expr (
  input  logic        clk,
  input  logic        a,
  input  logic [39:0] b,
  output logic [39:0] y,
  output logic [39:0] z,
  output logic [39:0] d
);
  assign y = 'bx;
  always_comb z = a ? 'hz1 : 40'd5;
  assign d = b | 'hx0;
endmodule
