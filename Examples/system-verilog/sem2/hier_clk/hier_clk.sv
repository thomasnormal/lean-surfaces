// F3 differential design: clocked children. A child flop whose clock port
// is connected to the parent's clock signal flattens to a parent-level
// flop; the `.clk` implicit named connection and a two-stage pipeline
// through output-port connections.
module hc_reg #(parameter int W = 4) (
  input  logic         clk,
  input  logic [W-1:0] d,
  output logic [W-1:0] q
);
  always_ff @(posedge clk) q <= d;
endmodule

module hier_clk #(parameter int W = 4) (
  input  logic         clk,
  input  logic [W-1:0] a,
  output logic [W-1:0] q2,
  output logic [W-1:0] s
);
  logic [W-1:0] q1;
  hc_reg #(.W(W)) r1 (.clk(clk), .d(a), .q(q1));
  hc_reg #(.W(W)) r2 (.clk, .d(q1 ^ a), .q(q2));
  assign s = q1 + q2;
endmodule
