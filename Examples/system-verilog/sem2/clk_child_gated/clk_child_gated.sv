// REFUSED by the clock discipline (`Instance:clock`, WP-Q0 reports the
// existing Hier2 kind at the loader): the child's clock port is connected to
// the GATED parent signal `g = clk & en`, not to the parent's clock port.
module clk_cg_reg (
  input  logic       clk, d,
  output logic       q
);
  always_ff @(posedge clk) q <= d;
endmodule

module clk_child_gated (
  input  logic clk, en, d,
  output logic q
);
  logic g;
  assign g = clk & en;
  clk_cg_reg u (.clk(g), .d(d), .q(q));
endmodule
