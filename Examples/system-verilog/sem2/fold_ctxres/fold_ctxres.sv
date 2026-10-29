// Round 3 folds, item 1 (context widths): at the default N = 2 the 4-bit
// sums are TRUNCATED to the 2-bit outputs (slang's tree holds an implicit
// conversion around them); at N > 4 the context is wider than the operands,
// which are extended BEFORE the operation (IEEE 1800-2023 11.8.2): the
// carry of `a + b`, the borrow of `a - b` and the high ones of `~a` survive.
module fold_ctxres #(parameter int N = 2) (
  input  logic [3:0]   a, b,
  output logic [N-1:0] c,
  output logic [N-1:0] d,
  output logic [N-1:0] e
);
  assign c = a + b;
  always_comb d = a - b;
  assign e = ~a;
endmodule
