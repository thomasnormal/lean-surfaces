// Minimal generic witness for the current front-end boundary.
module edge_child_canonical_e(input logic clk, input logic d, output logic q);
  always_ff @(posedge clk)
    q <= d;
endmodule
module edge_parent_canonical_e(input logic clk, input logic d, output logic y);
  logic q;
  edge_child_canonical_e u_child(.clk(clk), .d(d), .q(q));
  assign y = q;
endmodule
// End of witness.
