// Round 6 repair (T1 control, lane A, 2026-10-29): `Select:wide-index` judges
// only the generate code a parameter point INSTANTIATES. The wide-looking
// `v[a]` sits in the K == 1 arm; at N = 40, K = 0 that arm is not
// instantiated (the index of the live arm, a[3:0], is 4 bits), so every tool
// agrees and the design is admitted. N = 4, K = 1 is the live arm at a 4-bit
// index (admitted); N = 40, K = 1 is the live arm at a 40-bit index, where
// Xcelium (BIGWBS), Icarus and Verilator truncate the index to its low 32
// bits and the model refuses (`Select:wide-index`, row wide_index_dead_n40_live).
module wide_index_dead #(
  parameter int N = 4,
  parameter int K = 1
) (
  input  logic [N-1:0] a,
  input  logic [7:0]   v,
  output logic         o
);
  if (K == 1) begin : g_full
    assign o = v[a];
  end else begin : g_low
    assign o = v[a[3:0]];
  end
endmodule
