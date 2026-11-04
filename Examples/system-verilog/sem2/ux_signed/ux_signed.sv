// UNSIZED SIGNED BASED literals in expressions (round 5 Lane A,
// 2026-10-29). Icarus 12.0 sizes such a literal to its digits and
// sign-extends it in EVERY context: e1 = 'sb1 reads 11111111, e2 = 'sh8
// 11111000, e3 = a + 'sb1 is a - 1, localparam P = 'sh8 is -8, and a `case`
// item 'sb1 matches nothing 8 bits wide. Verilator 5.042 and Yosys 0.53
// (and IEEE 1800-2023 §5.7.1) read the digits zero-padded to 32 bits:
// 00000001, 00001000, a + 1, 8, item 1. The symbolic tier admitted these
// with the LRM value at 2e8c8b28 (a silent pick against the harness
// oracle); now loud (`IntegerLiteral:unsized-signed`, a scan of the
// sources, `_sym_unsized_signed_scan`).
module ux_signed (
  input  logic       clk,
  input  logic [7:0] a,
  output logic [7:0] e1,
  output logic [7:0] e2,
  output logic [7:0] e3,
  output logic [7:0] e4,
  output logic [7:0] e5
);
  localparam P = 'sh8;
  assign e1 = 'sb1;
  assign e2 = 'sh8;
  assign e3 = a + 'sb1;
  assign e4 = P;
  always_comb begin
    case (a)
      'sb1:    e5 = 8'd1;
      default: e5 = 8'd2;
    endcase
  end
endmodule
