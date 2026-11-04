// WP-B2 gate 2: `+` and `-` in the leaves of an always_comb tree. The two arms add and subtract the N-bit operands
// into an (N+1)-bit target (slang zero-extends each operand: the `Resize` marker), and the condition is a bare select.
module addp #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  input  logic         c,
  output logic [N:0]   y
);
  always_comb begin
    if (c) y = a + b; else y = a - b;
  end
endmodule
