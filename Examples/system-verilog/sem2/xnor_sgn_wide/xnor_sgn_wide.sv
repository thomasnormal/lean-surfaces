// REFUSED (loud, `ConversionExpression:width`; WP-L2): a signed operand PAIR whose result is
// assigned to a WIDER target needs sign extension of the operands before the operator (IEEE 1800-2023
// 11.8.2). The symbolic tier has no signed widening, so the existing `^` and `|` refuse the same text
// (`$signed(a) ^ $signed(b)` into a wider target); `~^` is lowered to `~(a ^ b)` and inherits the refusal.
module xnor_sgn_wide #(parameter int N = 4) (
  input  logic [N-1:0]   ua, ub,
  output logic [2*N-1:0] w
);
  assign w = $signed(ua) ~^ $signed(ub);
endmodule
