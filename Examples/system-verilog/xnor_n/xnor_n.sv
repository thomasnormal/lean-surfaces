// The N-bit bitwise XNOR, written with the native operator `~^` (WP-L2, 2026-10-30). The extractor
// lowers `a ~^ b` to `~(a ^ b)` (the nodes the symbolic tier already has), so the 4-state table is
// the product of the two pinned ones; `proof.lean` proves, for every width, that the lowered
// expression has exactly the IEEE 1800-2023 Table 11-14 value on every bit pair.
module xnor_n #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  output logic [N-1:0] y
);
  assign y = a ~^ b;
endmodule
