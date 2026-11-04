module symbolic_signed_2state #(parameter W = 4) (
  input bit signed [W-1:0] a,
  input bit signed [W-1:0] b,
  output bit signed [W-1:0] y
);
  assign y = (a < b) ? a : b;
endmodule
