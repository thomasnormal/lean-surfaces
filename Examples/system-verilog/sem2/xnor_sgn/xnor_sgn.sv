// `~^` over SIGNED operands (WP-L2, 2026-10-30). XNOR is bitwise, so signedness never changes a bit
// at the operands' own width: `same` is the plain table. Mixed signedness makes the expression
// unsigned (IEEE 1800-2023 11.8.1), so `mixed` zero-extends the signed side before the operator.
// A signed PAIR into a wider target would sign-extend: that is the tier's existing loud
// `ConversionExpression:width` for every bitwise operator (see xnor_sgn_wide).
module xnor_sgn #(parameter int N = 4) (
  input  logic [N-1:0]   ua, ub,
  output logic [N-1:0]   same,    // $signed(ua) ~^ $signed(ub): a signed pair at its own width
  output logic [2*N-1:0] mixed    // signed ^~ unsigned: unsigned, zero-extended to 2N
);
  assign same  = $signed(ua) ~^ $signed(ub);
  assign mixed = $signed(ua) ^~ ub;
endmodule
