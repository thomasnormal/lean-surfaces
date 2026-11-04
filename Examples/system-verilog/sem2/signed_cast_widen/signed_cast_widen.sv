// A fixed-width typedef cast sign-extends its signed source operand.
module signed_cast_widen (
  input  logic signed [3:0] a,
  output logic signed [7:0] y
);
  typedef logic signed [7:0] wide_t;
  always_comb y = wide_t'(a);
endmodule
