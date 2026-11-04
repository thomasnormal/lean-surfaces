// Round 6 repair (T1, lane A, 2026-10-29): a bit-select WRITE whose index is
// already wider than 32 bits at the default point (40 bits). The extractor
// refuses the select; a refused select leaves no usable assignment target, so
// the Unsupported node that reaches the envelope is the assignment's
// (`AssignmentExpression:target`), not `ElementSelectExpression:wide-index`
// (the read tag, row wide_index_lit). Xcelium 24.03-s004 (BIGWBS) writes
// w[a] at the index truncated to 32 bits; Icarus 12.0 drops the write; the
// LRM (11.5.1) writes nothing for an out-of-range index.
module wide_index_wr (
  input  logic [39:0] a,
  input  logic        b,
  output logic [7:0]  w
);
  always_comb begin
    w = '0;
    w[a] = b;
  end
endmodule
