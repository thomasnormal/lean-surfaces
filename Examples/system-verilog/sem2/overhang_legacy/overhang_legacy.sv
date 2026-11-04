// Round 6 (Xcelium audit clusters P1/P3, lane A, 2026-10-29): the LEGACY
// part-select encoding. A range select [K+2:K] over the literal range [7:0]
// keeps the legacy `PartSel` (offsets from bit 0) and lowers to a constant
// slice that x-pads silently past the vector's msb. At K = 6 the select
// [8:6] is PARTLY out of range: IEEE 1800-2023 11.5.1 reads x in bit 8 only
// (and a write changes bits 7:6 only), Xcelium 24.03-s004 reads the whole
// select as x and drops the write. Refused (`Select:partial-overhang`,
// RangeGuard2.lean). In range (K = 2) and wholly out of range (K = 9: x
// read, no-op write, every tool agrees) stay admitted.
module overhang_legacy #(parameter int K = 2) (
  input  logic [7:0] v,
  input  logic [2:0] b,
  output logic [2:0] y,
  output logic [7:0] w
);
  assign y = v[K+2:K];
  always_comb begin
    w = '0;
    w[K+2:K] = b;
  end
endmodule
