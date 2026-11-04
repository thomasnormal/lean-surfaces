// WP-B2 gate 3: a shift into a WIDER target. The left operand is zero-extended to the context width BEFORE the
// shift (slang's `Resize` marker), so the bits shifted out of an `N`-bit operand survive in an `(N+1)`-bit target.
module shl_wide #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [2:0]   s,
  output logic [N:0]   y
);
  assign y = a << s;
endmodule
