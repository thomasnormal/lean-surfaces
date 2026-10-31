// WP-G S2 negative: `!s` into a 4-bit target: slang wraps the 1-bit logical result in a zero-extension.
module neg_lnot_wide (input logic s, output logic [3:0] y);
  assign y = !s;
endmodule
