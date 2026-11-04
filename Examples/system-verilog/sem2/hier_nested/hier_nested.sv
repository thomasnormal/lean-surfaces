// F3 differential design: a three-level hierarchy (hier_nested -> hn_mid ->
// hn_leaf), instances inside a generate-for and a generate-if, implicit
// `.*` connections, unconnected input ports (a net reads z, a `var`
// variable x) and an unconnected output.
module hn_leaf #(parameter int W = 1) (
  input  logic [W-1:0] p,
  input  logic [W-1:0] q,
  output logic [W-1:0] r
);
  assign r = p & q;
endmodule

module hn_mid #(parameter int W = 2) (
  input  logic [W-1:0] p,
  input  logic [W-1:0] q,
  output logic [W-1:0] r,
  output logic [W-1:0] t
);
  hn_leaf #(.W(W)) l0 (.p(p), .q(q), .r(r));
  hn_leaf #(.W(W)) l1 (.p(p), .q(~q), .r(t));
endmodule

module hn_unc (
  input  logic       en,
  input  var logic   vin,
  input  logic [1:0] d,
  output logic [1:0] y,
  output logic       u
);
  assign y = {en, vin};
  assign u = ^d;
endmodule

module hier_nested #(parameter int N = 3) (
  input  logic [N-1:0] p,
  input  logic [N-1:0] q,
  output logic [N-1:0] r,
  output logic [N-1:0] t,
  output logic [N-1:0] g,
  output logic [1:0]   z
);
  if (N > 2) begin : g_mid
    hn_mid #(.W(N)) m (.*);
  end else begin : g_flat
    assign r = p | q;
    assign t = p ^ q;
  end
  for (genvar k = 0; k < N; k++) begin : g_bit
    hn_leaf b (.p(p[k]), .q(q[N-1-k]), .r(g[k]));
  end
  hn_unc un (.en(), .vin(), .d(p[1:0]), .y(z), .u());
endmodule
