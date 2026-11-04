// WP-B2 gate 3: a one-hot decoder, the unsized constant `1` shifted by a run-time amount. The constant is 32 bits
// wide, so the shift is computed at `max N 32` bits and the result is truncated into the target.
module onehot #(parameter int N = 4) (
  input  logic [2:0]   s,
  output logic [N-1:0] y
);
  assign y = 1 << s;
endmodule
