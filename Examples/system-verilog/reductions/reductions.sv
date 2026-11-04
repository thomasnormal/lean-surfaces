module reductions(
  input logic [3:0] a,
  output logic red_or,
  output logic red_and,
  output logic red_xor,
  output logic red_nor,
  output logic red_nand,
  output logic red_xnor);
  assign red_or = |a;
  assign red_and = &a;
  assign red_xor = ^a;
  assign red_nor = ~|a;
  assign red_nand = ~&a;
  assign red_xnor = ~^a;
endmodule
