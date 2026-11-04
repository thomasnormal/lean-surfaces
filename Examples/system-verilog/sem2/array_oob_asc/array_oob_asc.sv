// An element label outside an ASCENDING packed dimension, read from a
// NON-last element: the half of the former `array_oob_part` that round 6
// (2026-10-29) leaves admitted. `q[0][4]` is a single bit whose label lies
// outside `[0:3]`; IEEE 1800-2023 11.5.1 reads x, and so do the model and
// Xcelium 24.03-s004 (pinned, docs/sv-xcelium-audit.md). Icarus 12.0 and
// Yosys 0.53 linearize it into the neighbouring element (`q[0][4]` reads
// `q[1][0]`): a declared Icarus disagreement, docs/sv-oracle-disagreements.md
// "Linearized packed-array indices". The part-selects that overhang an inner
// dimension (`m[0][5:3]`, `q[0][2 +: 3]`, `q[1][-1 +: 2]`) and the overhanging
// write `w[0][5:2] = a` are the loud-refusal row `array_oob_part`.
module array_oob_asc (
  input  logic [7:0] src,
  output logic       asc_oob
);
  logic [0:1][0:3] q;
  assign q = src;
  always_comb begin
    asc_oob = q[0][4];
  end
endmodule
