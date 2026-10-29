// Round 6 (Xcelium audit cluster T1, lane A, 2026-10-29): a CONSTANT bit
// select index of 2^32 or more. IEEE 1800-2023 11.5.1: 2^32 + 2 is outside
// [7:0], x; Xcelium 24.03-s004 (BIGWBS in xmvlog and xmelab) truncates the
// constant to its low 32 bits and reads v[2]; Icarus 12.0 and the model read x.
// Refused by the extractor (`ElementSelectExpression:wide-index`); a wider
// constant whose value fits (40'd2) stays admitted.
module wide_index_const (
  input  logic [7:0] v,
  output logic       o
);
  assign o = v[40'h1_0000_0002];
endmodule
