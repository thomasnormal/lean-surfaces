// Clean-room F1 witness for four-state sampled knownness.
module sva_isunknown (
  input logic clk,
  input logic a,
  output logic q
);
  assign q = a;
  assert property (@(posedge clk) !$isunknown(a));
endmodule
