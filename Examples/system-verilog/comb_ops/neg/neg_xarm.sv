// WP-G S2 negative: an x literal arm: a literal with an unknown bit is not in the equation fragment.
module neg_xarm (input logic [3:0] a, input logic s, output logic [3:0] y);
  assign y = s ? a : 4'bxxxx;
endmodule
