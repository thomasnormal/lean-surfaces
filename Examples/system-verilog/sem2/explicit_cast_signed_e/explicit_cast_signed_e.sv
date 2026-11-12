module explicit_cast_signed_e #(parameter int W = 8) (input logic signed [3:0] x, input bit [3:0] b, output logic [W-1:0] ys, output logic [W-1:0] yb);
  assign ys = W'(x);
  assign yb = W'(b);
endmodule
