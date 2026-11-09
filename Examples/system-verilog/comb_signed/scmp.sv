// The four signed comparisons of two signed operands of one width W (IEEE 1800-2023 §11.4.4, §11.8.1): both operands
// are signed, so they are ordered as two's-complement integers, and each result is one unsigned bit.
module scmp #(parameter integer W = 8) (
  input  logic signed [W-1:0] a, b,
  output logic lt, le, gt, ge
);
  assign lt = a < b;
  assign le = a <= b;
  assign gt = a > b;
  assign ge = a >= b;
endmodule
