module signed_exponent_power #(parameter W = 8, parameter E = 4)
  (input logic [W-1:0] base, input logic [E-1:0] exponent,
   output logic [W-1:0] result);
  assign result = base ** $signed(exponent);
endmodule
