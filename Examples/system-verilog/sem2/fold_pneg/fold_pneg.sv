// Round 3 folds, item 1: a NEGATIVE int parameter or localparam
// used as a simple operand in an UNSIGNED context. At the default N = 7 the
// context is 32 bits wide (the int's own width); where `a` is wider than 32
// bits (N >= 31) IEEE 1800-2023 11.8.2 zero-extends the operand (it is
// converted to the unsigned context type first), while an assignment-like
// conversion (`o4 = P`) keeps the right-hand side's signedness and
// sign-extends. (A negative GENVAR in the same position splits the oracles:
// fixture `fold_pgen`.)
module fold_pneg #(parameter int N = 7, parameter int P = -3) (
  input  logic [N+1:0] a,
  output logic [N+1:0] o1,
  output logic [N+1:0] o2,
  output logic         o3,
  output logic [N+1:0] o4,
  output logic [N+1:0] o5,
  output logic [N+1:0] o6
);
  localparam int M = -5;
  assign o1 = a + P;
  assign o2 = a & P;
  assign o3 = (a == P);
  assign o4 = P;
  assign o5 = a + P * 2;
  assign o6 = a | M;
endmodule
