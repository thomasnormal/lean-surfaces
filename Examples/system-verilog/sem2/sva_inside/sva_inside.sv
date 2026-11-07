// Clean-room F1 witness for a finite SVA inside set.
module sva_inside (
  input logic clk,
  input logic a,
  output logic q
);
  assign q = a;
  assert property (@(posedge clk) a inside {1'b0, 1'b1});
endmodule
