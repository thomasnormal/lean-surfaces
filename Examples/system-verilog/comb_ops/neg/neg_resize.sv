// WP-G S2 negative: `~a` into a wider target. slang inserts an implicit zero-extension of the operand
// (the context-determined `~` is applied to the EXTENDED operand): a width conversion, outside the fragment.
module neg_resize (input logic [3:0] a, output logic [4:0] y);
  assign y = ~a;
endmodule
