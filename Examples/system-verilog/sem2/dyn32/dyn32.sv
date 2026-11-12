// Run-time indexed part-select bases of EXACTLY 32 bits (verifier probes
// pa/pb, 2026-10-28). `s - 2` is 32-bit unsigned (the unsized `2` widens
// `s`), so an underflow is a large unsigned address and reads all x under
// IEEE 1800-2023 §11.8.1. The E model follows that typing rule. Bases wider
// than 32 bits are refused (the tools disagree there). Rows:
// harness/sv/cases2.json `dyn32` and `dyn32_part`.
//
// Xcelium 24.03-s004 (the reference simulator) reads such a base as UNSIGNED,
// as the typing rules of IEEE 1800-2023 11.8.1 imply: `s - 2` at s = 0 is
// 32'hFFFFFFFE, wholly out of range, all x. Xcelium also returns all x for a
// base that leaves the vector only PARTLY, where the model reads the LRM's
// per-bit value (11.5.1): a declared departure on `dyn32`, `dyn32_part` and
// `partsel_dyn*` (docs/sv-oracle-disagreements.md, "Run-time part-select bases
// that leave the vector"). Icarus Verilog 13.0 matches the model on these rows.
module dyn32 (
  input  logic [7:0]  v,
  input  logic [3:0]  s,
  input  logic [31:0] b32,
  output logic [3:0]  minus2,
  output logic [3:0]  minus2_dn,
  output logic [3:0]  m32,
  output logic [3:0]  o32,
  output logic [3:0]  d32
);
  assign minus2    = v[s - 2 +: 4];
  assign minus2_dn = v[s - 2 -: 4];
  assign m32       = v[{28'b0, s} - 32'd2 +: 4];
  assign o32       = v[b32 +: 4];
  assign d32       = v[b32 -: 4];
endmodule
