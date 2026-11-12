module explicit_cast_e #(parameter int W = 8) (input logic [3:0] x, output logic [W-1:0] y);
  assign y = W'(x);
endmodule
