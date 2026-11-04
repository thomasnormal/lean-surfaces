// Round 3 folds, item 1 (typed signed parameters): a `byte` parameter as a
// simple operand in an unsigned context of its own width at the default
// point (`a + B` into 8 bits) is zero-extended where the context is wider
// (`o8`, `[N:0]`, at N > 7); a comparison of two signed operands and
// assignment-like conversions keep their signedness.
module fold_sparam #(parameter int N = 7, parameter logic signed [3:0] S = -4'sd2,
                     parameter byte B = -3) (
  input  logic [3:0] a,
  output logic       c1,
  output logic       c2,
  output logic [7:0] o6,
  output logic [N:0] o8
);
  assign c1 = B < -1;
  assign c2 = S < 0;
  assign o6 = a + B;
  assign o8 = a + B;
endmodule
