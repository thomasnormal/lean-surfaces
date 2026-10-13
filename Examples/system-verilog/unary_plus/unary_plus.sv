module unary_plus(
  input logic [3:0] a,
  output logic [3:0] b,
  output logic [3:0] c);
  assign b = +a;
  assign c = +(4'b0101);
endmodule
