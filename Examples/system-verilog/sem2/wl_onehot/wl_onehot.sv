// WP-B2 gate 3 pin P16: `1 << s`: the unsized constant `1` is a signed 32-bit integer, so the shift is computed at max(target, 32) bits (the sign extension of 1 is zero) and truncated into the target: 4 bits, 33 and 40 bits (`s = 33` sets bit 33 of a 40-bit target, `s = 40` gives 0). `1'b1 << s` (a sized, unsigned operand) agrees. An x/z bit of the amount makes every result bit x.
module wl_onehot #(parameter int N = 4) (
  input  logic [5:0] s,
  output logic [N-1:0] y,
  output logic [39:0] w,
  output logic [39:0] u
);
  assign y = 1 << s;
  assign w = 1 << s;
  assign u = 1'b1 << s;
endmodule
