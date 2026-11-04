// WP-B2 gate 3b: concatenations as operands of word-level operators. In `s` the operands `{1'b0, a}` are exactly as wide
// as the sum (bare concatenations), `cin` is zero-extended by slang's `Resize` marker; in `t` the second operand `{b, 1'b0}`
// is one bit narrower than the sum, so a `Resize` marker sits around the concatenation itself. `w` takes concatenations
// in the arms of `?:`, `e` compares two of them.
module cat_add #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [N-1:0] b,
  input  logic         cin,
  output logic [N:0]   s,
  output logic [N+1:0] t,
  output logic [N:0]   w,
  output logic         e
);
  assign s = {1'b0, a} + {1'b0, b} + cin;
  assign t = {2'b0, a} + {b, 1'b0};
  assign w = cin ? {a, 1'b0} : {1'b1, a};
  assign e = {a, b} == {b, a};
endmodule
