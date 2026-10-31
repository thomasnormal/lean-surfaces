// WP-G S2: a multi-bit condition is accepted by the recognizer (reductions are the way to say "any bit set":
// `|v ? a : b`), and the obligation `width` is then FALSE: the condition must be one bit wide.
module neg_tern_wide #(parameter int N = 4) (input logic [N-1:0] v, a, b, output logic [N-1:0] y);
  assign y = v ? a : b;
endmodule
