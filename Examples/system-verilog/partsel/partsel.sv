// Indexed part-selects (IEEE 1800-2023 11.5.1) whose bases are
// elaboration-time constants over parameters and genvars, as continuous-
// assign targets and reads; selects that leave the vector at some parameter
// points (out-of-range bits read x, writes to them do nothing); and run-time
// (signal) bases in reads.
module partsel #(parameter int N = 4, parameter int W = 3) (
  input  logic [N*W-1:0] a,        // N lanes of W bits
  input  logic [7:0]     v,
  input  logic [2:0]     sel,
  input  logic [3:0]     b,
  output logic [N*W-1:0] rev_up,   // lanes reversed with +:
  output logic [N*W-1:0] rev_dn,   // the same permutation with -:
  output logic [N-1:0]   top,      // a[N*W-1 -: N]
  output logic [3:0]     ov_hi,    // two bits above the msb
  output logic [3:0]     ov_lo,    // below the lsb when W < 5
  output logic [3:0]     ov_rng,   // a range select above the msb
  output logic [3:0]     dyn_up,   // v[sel +: 4]
  output logic [3:0]     dyn_dn,   // v[sel -: 4]
  output logic [W-1:0]   dyn_lane, // lane sel of a (x past the last lane)
  output logic [7:0]     w_hi,     // write overhanging the msb when N > 1
  output logic [7:0]     w_lo      // write overhanging the lsb when N < 6
);
  genvar i;
  for (i = 0; i < N; i++) begin : g_rev
    assign rev_up[i*W +: W] = a[(N-1-i)*W +: W];
    assign rev_dn[(i+1)*W-1 -: W] = a[(N-i)*W-1 -: W];
  end
  assign top      = a[N*W-1 -: N];
  assign ov_hi    = a[N*W-2 +: 4];
  assign ov_lo    = a[W-2 -: 4];
  assign ov_rng   = a[N*W+1 : N*W-2];
  assign dyn_up   = v[sel +: 4];
  assign dyn_dn   = v[sel -: 4];
  assign dyn_lane = a[sel*W +: W];
  always_comb begin
    w_hi = '0;
    w_hi[N+3 +: 4] = b;
  end
  always_comb begin
    w_lo = '0;
    w_lo[N-3 -: 4] = b;
  end
endmodule
