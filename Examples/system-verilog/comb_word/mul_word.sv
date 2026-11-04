// `*` in the sv_comb fragment: one product into an N-bit target (the product modulo 2^N) and the same product into a
// 2N-bit target (slang zero-extends each factor to the 2N-bit context first: the full product, no overflow).
module mul_word #(parameter int N = 4) (
  input  logic [N-1:0]   a, b,
  output logic [N-1:0]   p,
  output logic [2*N-1:0] q
);
  assign p = a * b;
  assign q = a * b;
endmodule
