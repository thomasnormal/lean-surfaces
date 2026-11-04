// Generate-loop genvars that REUSE the name of a parameter appearing in a
// packed array's declared range (legal SV: the genvar shadows the parameter
// only inside the loop). The array's geometry is the declaration's - the
// module's K and W - never the genvar's: `m[1][0]` is flat bit K+1, and
// `t[r][K]` (genvar K) writes element r's label K of [K:0] (module K).
// Reads (`y`, `z`) and targets (`t`) both pinned against Icarus.
module array_gvshadow #(parameter int K = 2, parameter int W = 4) (
  input  logic [4*(K+1)-1:0] src,
  input  logic [2*W-1:0]     u,
  output logic               y,
  output logic [1:0]         z,
  output logic [4*(K+1)-1:0] t_flat
);
  localparam int KK = K;
  logic [3:0][K:0]   m;
  logic [3:0][K:0]   t;
  logic [1:0][W-1:0] n;
  assign m = src;
  assign n = u;
  for (genvar K = 1; K < 2; K++) begin : g_read
    assign y = m[1][0];
  end
  for (genvar W = 0; W < 2; W++) begin : g_row
    assign z[W] = n[W][W+2];
  end
  for (genvar K = 0; K <= KK; K++) begin : g_col
    for (genvar r = 0; r < 4; r++) begin : g_el
      assign t[r][K] = src[r*(KK+1) + (KK-K)];
    end
  end
  assign t_flat = t;
endmodule
