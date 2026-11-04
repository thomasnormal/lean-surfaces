// WP-G four-state contract: `c ? ~a : 4'b0000` with a 1-bit a: the arm ~a is context-determined, extended to 4 bits before the inversion (111~a), and a merge of 111~a with 0000 under c = x is xxx~a-or-x. Pinned against Xcelium 24.03.
module wpg_tern_ctx (
  input  logic a,
  input  logic c,
  output logic [3:0] y
);
  assign y = c ? ~a : 4'b0000;
endmodule
