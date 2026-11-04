// WP-B2 gate 2b pin P12: a sum into a NARROWER target is the low bits of the sum formed at the operands' width (truncation marker); `a + 1` is a 32-bit sum truncated to the target; `a - 1` into 5 bits is a 32-bit difference truncated to 5 (the borrow of `0 - 1` fills the low 5 bits).
module wl_trunc_inc (
  input  logic [3:0] a,
  input  logic [3:0] b,
  output logic [2:0] t,
  output logic [3:0] y1,
  output logic [4:0] y2
);
  assign t = a + b;
  assign y1 = a + 1;
  assign y2 = a - 1;
endmodule
