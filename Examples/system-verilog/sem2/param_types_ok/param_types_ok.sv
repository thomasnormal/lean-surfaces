// Parameter TYPES in constant select labels (IEEE 1800-2023 6.20.2,
// verifier finding 2026-10-28). A range without a type (`[3:0] V4`) is
// unsigned at that range whatever the override (an override of 25 reads 9);
// a parameter with neither (`P = 3'd5`) has its default's type where it is
// NOT overridden (`P + 3'd4` wraps to 1 there) and the integer override's
// (`int`) where it is; `signed [3:0]`, `logic signed [3:0]`, `bit [4:0]`
// and `byte` keep their declared width and signedness, so a narrow signed
// parameter sign-extends in `S4 + 3`. Rows: harness/sv/cases2.json
// `param_types*` (Icarus 12.0; Yosys 0.53 agrees at the checked points).
//
// ROUND 6 SPLIT (2026-10-29). This is `param_types` WITHOUT `o_sb` and `o_b5`:
// those two selects (`v[SB + 5 +: 4]`, `v[B5 + 5'd4 -: 4]`) leave the 16-bit `v`
// PARTLY at the original rows' points (B5 = 30 wraps to label 2, so `-: 4` covers
// labels 2 .. -1; SB = -7 gives labels -2 .. 1), and Xcelium 24.03-s004 reads such
// a select as all x where IEEE 1800-2023 11.5.1 (and the model, Icarus, Yosys)
// read x in the out-of-range bits only (docs/sv-xcelium-audit.md, P1). The model
// refuses them (`ArraySel:partial-overhang`), so every `param_types*` row is a
// loud-refusal row; the parameter-type outputs that stay in range live on here,
// rows `param_types_ok*`, equal in the model, Icarus and Xcelium.
module param_types_ok #(
  parameter P = 3'd5,                     // untyped, sized default
  parameter [3:0] V4 = 4'd9,              // range, no type: 4-bit unsigned
  parameter signed [3:0] SV4 = -4'sd2,    // signed range: 4-bit signed
  parameter [31:0] U32 = 5,               // a 32-bit UNSIGNED range
  parameter logic signed [3:0] S4 = -4'sd2,
  parameter bit [4:0] B5 = 5'd30,
  parameter byte SB = -8'sd3,
  parameter Q = 4                         // untyped, int default
) (
  input  logic [15:0] v,
  output logic [1:0]  o_p,     // P + 3'd4: 3-bit wrap at the default
  output logic [1:0]  o_v,     // V4 + 4'd8: 4-bit wrap
  output logic [1:0]  o_v2,    // V4 truncates an override
  output logic [1:0]  o_q,
  output logic [1:0]  o_sv,    // SV4 + 4'sd7: 4-bit signed wrap
  output logic [1:0]  o_u,     // U32 - 6 is unsigned
  output logic [3:0]  o_s1,    // S4 + 3 (S4 sign-extended to int)
  output logic [3:0]  o_s2,    // (S4 >>> 1) + 4
  output logic [3:0]  o_s3     // S4 * -1
);
  assign o_p  = v[P + 3'd4 +: 2];
  assign o_v  = v[V4 + 4'd8 +: 2];
  assign o_v2 = v[V4 -: 2];
  assign o_q  = v[Q + 3'd4 +: 2];
  assign o_sv = v[SV4 + 4'sd7 +: 2];
  assign o_u  = (U32 - 6 > 100) ? 2'b10 : 2'b01;
  assign o_s1 = v[S4 + 3 +: 4];
  assign o_s2 = v[(S4 >>> 1) + 4 +: 4];
  assign o_s3 = v[S4 * -1 +: 4];
endmodule
