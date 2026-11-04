// WP-B2: `a + b` into a target ONE bit wider. The context is N+1 bits, so slang wraps each operand in a
// zero-extension (`Resize`) and the carry survives in y[N].
module add_wide #(parameter int N = 8) (
  input  logic [N-1:0] a, b,
  output logic [N:0]   y
);
  assign y = a + b;
endmodule
