// A SIGNED operand that reads a signal, widened by a parameter-dependent
// context: refused as a width conversion (`ConversionExpression:width`),
// not mislabelled a signed constant.
module signed_operand #(parameter int N = 7) (
  input  logic [3:0] a,
  output logic [N:0] o
);
  assign o = $signed(a) * -2;
endmodule
