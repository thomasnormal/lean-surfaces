// One driver per bit on an instance-free top (2026-10-28, WP2): the
// windows of a generate-for's continuous assigns depend on the genvar and
// the parameter, and are pairwise disjoint at every point — `y[2i +: 2]`
// for `i < N` tiles `y` — so the one-driver rule admits the design at
// every `N` and the differential rows compare it with Icarus.
module drv_genvar_disj #(parameter int N = 4) (
  input  logic [N-1:0]   a,
  input  logic [N-1:0]   b,
  output logic [2*N-1:0] y
);
  for (genvar i = 0; i < N; i++) begin : g
    assign y[2*i +: 2] = {a[i], b[N-1-i]};
  end
endmodule
