module context_power #(parameter W = 8)
  (input logic [7:0] base, input logic [3:0] exponent,
   output logic [W-1:0] result, negative_square, concat_square);
  assign result = base ** $signed(exponent);
  assign negative_square = (-8'sh80) ** 2;
  assign concat_square = {((-8'sh80) ** 2)};
endmodule
