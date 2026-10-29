// F3 differential design: INTEGER constants (unsized decimals, negations,
// genvars, parameter expressions) as input-port actuals, into ports whose
// width varies per instance — by a genvar inside a generate-for and by the
// top's parameter `N`. slang binds each actual converted to the port of the
// instance it bound (the defaults / the FIRST generate iteration); the
// extractor emits the unconverted INT-class tree and the Lean side fits it
// to each port's own width (2026-10-28 verifier finding: `.i(5)` used to be
// a 1-bit literal everywhere). Also: two instance outputs on DISJOINT bits
// of one signal (`pair`), which the one-driver rule admits.
module ia_pass #(parameter int W = 1) (
  input  logic [W-1:0] i,
  output logic [W-1:0] o
);
  assign o = i;
endmodule

module hier_intact #(parameter int N = 4) (
  input  logic [1:0]   a,
  output logic [5:0]   five,
  output logic [5:0]   neg,
  output logic [5:0]   gv,
  output logic [5:0]   sized,
  output logic [N+1:0] o1,
  output logic [N+1:0] o2,
  output logic [N-1:0] big,
  output logic [1:0]   pair
);
  // A module-level `genvar` (Icarus 12.0 refuses an inline `for (genvar g …)`
  // whose genvar is an input actual: "A reference to a wire or reg (`g') is
  // not allowed in a constant expression").
  genvar g;
  for (g = 1; g <= 3; g++) begin : gl
    ia_pass #(.W(g)) pf (.i(5),    .o(five[(g*(g-1))/2 +: g]));
    ia_pass #(.W(g)) pn (.i(-1),   .o(neg[(g*(g-1))/2 +: g]));
    ia_pass #(.W(g)) pg (.i(g),    .o(gv[(g*(g-1))/2 +: g]));
    ia_pass #(.W(g)) ps (.i(3'd5), .o(sized[(g*(g-1))/2 +: g]));
  end
  ia_pass #(.W(N+2)) c1 (.i(-1),    .o(o1));
  ia_pass #(.W(N+2)) c2 (.i(N*3-1), .o(o2));
  ia_pass #(.W(N))   pb (.i(37),    .o(big));
  logic [1:0] pv;
  ia_pass q0 (.i(a[0]), .o(pv[0]));
  ia_pass q1 (.i(a[1]), .o(pv[1]));
  assign pair = pv;
endmodule
