// `*` negative: neither factor is a signal access (the fragment reads a product with at least one; the elaboration
// folds a product of constants). Write one factor into a signal first.
module neg_mul_op #(parameter int N = 4) (input logic [N-1:0] a, b, output logic [N-1:0] y);
  assign y = (a + b) * (a - b);
endmodule
