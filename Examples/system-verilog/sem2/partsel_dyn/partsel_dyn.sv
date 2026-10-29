// The part of the `partsel` family that round 6 (2026-10-29) leaves admitted:
// indexed part-selects whose bases are elaboration-time constants over
// parameters and genvars and that stay IN RANGE (rev_up, rev_dn, top), and
// run-time (signal) bases in reads (dyn_up, dyn_dn, dyn_lane). The selects
// that leave the vector at some parameter point (`ov_hi`, `ov_lo`, `ov_rng`,
// the writes `w_hi`, `w_lo`) are the loud-refusal rows `partsel*`: IEEE
// 1800-2023 11.5.1 reads x in exactly the out-of-range bits and writes only
// the in-range ones, but Xcelium 24.03-s004 treats a part-select that is only
// partly in range as wholly invalid, so the tools split
// (docs/sv-xcelium-audit.md, P1 and P3).
//
// `dyn_up` and `dyn_dn` DO leave the vector for some `sel` (sel > 4 for
// `+:`, sel < 3 for `-:`) and cannot be refused statically: the model, Icarus
// 12.0 and Yosys 0.53 follow the LRM (x only for the out-of-range bits) and
// Xcelium returns all x for the whole select. That is a DECLARED Xcelium
// departure on rows `partsel_dyn*` (cluster P2, docs/sv-oracle-disagreements.md,
// "Run-time part-select bases that leave the vector").
module partsel_dyn #(parameter int N = 4, parameter int W = 3) (
  input  logic [N*W-1:0] a,        // N lanes of W bits
  input  logic [7:0]     v,
  input  logic [2:0]     sel,
  output logic [N*W-1:0] rev_up,   // lanes reversed with +:
  output logic [N*W-1:0] rev_dn,   // the same permutation with -:
  output logic [N-1:0]   top,      // a[N*W-1 -: N]
  output logic [3:0]     dyn_up,   // v[sel +: 4]
  output logic [3:0]     dyn_dn,   // v[sel -: 4]
  output logic [W-1:0]   dyn_lane  // lane sel of a (x past the last lane)
);
  genvar i;
  for (i = 0; i < N; i++) begin : g_rev
    assign rev_up[i*W +: W] = a[(N-1-i)*W +: W];
    assign rev_dn[(i+1)*W-1 -: W] = a[(N-i)*W-1 -: W];
  end
  assign top      = a[N*W-1 -: N];
  assign dyn_up   = v[sel +: 4];
  assign dyn_dn   = v[sel -: 4];
  assign dyn_lane = a[sel*W +: W];
endmodule
