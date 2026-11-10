// Clean-room memory-route fixture for a parser-shaped
// ConversionExpression:unsized-xz nested in a conditional expression.
// IEEE 1800-2023 §5.7.1 sizes an unsized x/z literal from the expression
// context: low bits survive truncation and the literal's most-significant
// x/z bit is replicated when the destination is wider.
module unsized_xz_ternary_mem #(
  parameter int N = 40
) (
  input  logic         clk,
  input  logic         a,
  output logic [N-1:0] y,
  output logic [N-1:0] mem_q
);
  logic [N-1:0] mem [0:N-1];

  assign y = a ? 'hz1 : 'b0;
  assign mem_q = mem[a];
endmodule
