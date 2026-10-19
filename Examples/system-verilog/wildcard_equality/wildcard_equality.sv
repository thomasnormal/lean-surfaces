module wildcard_equality #(parameter W = 4)
  (input logic [W-1:0] left, right, output logic equal, different);
  assign equal = left ==? right;
  assign different = left !=? right;
endmodule
