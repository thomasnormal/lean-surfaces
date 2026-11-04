module shifts #(parameter W = 8, parameter A = 4)
  (input logic [W-1:0] value, input logic [A-1:0] amount,
   output logic [W-1:0] logical_left, logical_right, arithmetic_left, arithmetic_right);
  assign logical_left = value << amount;
  assign logical_right = value >> amount;
  assign arithmetic_left = value <<< amount;
  assign arithmetic_right = $signed(value) >>> amount;
endmodule
