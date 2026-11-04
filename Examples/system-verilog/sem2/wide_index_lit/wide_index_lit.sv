// Round 6 (Xcelium audit cluster T1, lane A, 2026-10-29): a run-time bit
// select whose index is wider than 32 bits already at the DEFAULT point (a
// literal-bounds 33-bit `a`; compare wide_index, where the width depends on
// the parameter and only the Lean select guard sees it). IEEE 1800-2023
// 11.5.1 takes the index whole (a = 2^32 + 2 is out of range: x); Xcelium
// 24.03-s004 (BIGWBS), Icarus 12.0 and Verilator 5.042 read its low 32 bits
// (v[2]). The extractor refuses the select (`ElementSelectExpression:
// wide-index`), the model does not truncate.
module wide_index_lit (
  input  logic [32:0] a,
  input  logic [7:0]  v,
  output logic        o
);
  assign o = v[a];
endmodule
