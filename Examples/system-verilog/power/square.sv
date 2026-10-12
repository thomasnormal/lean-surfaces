module square #(parameter W = 8)
  (input logic [W-1:0] base, output logic [W-1:0] result);
  assign result = base ** 2;
endmodule
