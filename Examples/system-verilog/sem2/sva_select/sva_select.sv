// Clean-room F1 witness for a dynamic packed element select in an SVA property.
module sva_select (
  input logic clk,
  input logic [3:0] a,
  input logic [1:0] i,
  output logic q
);
  assign q = a[i];
  assert property (@(posedge clk) a[i] == q);
endmodule
