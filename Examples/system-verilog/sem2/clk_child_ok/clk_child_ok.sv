// ACCEPTED by the clock discipline (WP-Q0): a child register clocked through
// a bare connection to the parent's input-port clock, nothing reading the
// clock as data. The connection assign `u.ck = clk` is a plain copy that
// nothing reads.
module clk_co_reg (
  input  logic ck, d,
  output logic q
);
  always_ff @(posedge ck) q <= d;
endmodule

module clk_child_ok (
  input  logic clk, d,
  output logic q
);
  clk_co_reg u (.ck(clk), .d(d), .q(q));
endmodule
