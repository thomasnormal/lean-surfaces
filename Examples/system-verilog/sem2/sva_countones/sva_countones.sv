// Clean-room F1 witness for sampled $countones.
module sva_countones (
  input logic clk,
  input logic [3:0] a,
  output logic [31:0] q
);
  assign q = $countones(a);
  assert property (@(posedge clk) $countones(a) == q);
endmodule
