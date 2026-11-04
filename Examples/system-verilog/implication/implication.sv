module implication #(parameter W = 4)
  (input logic [W-1:0] left, right, output logic implied);
  assign implied = left -> right;
endmodule
