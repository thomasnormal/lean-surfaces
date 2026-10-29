// Run-time indexed part-select bases of EXACTLY 32 bits (verifier probes
// pa/pb, 2026-10-28). `s - 2` is 32-bit unsigned (the unsized `2` widens
// `s`), yet Icarus 12.0 and Yosys 0.53 both read a 32-bit index as a
// two's-complement int: `v[s - 2 +: 4]` at s = 0 is v[1:-2], two bits in
// range. The model reads it the same way (Param2 `dynPartRead32`). Bases
// wider than 32 bits are refused (the tools disagree there). Rows:
// harness/sv/cases2.json `dyn32`.
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
