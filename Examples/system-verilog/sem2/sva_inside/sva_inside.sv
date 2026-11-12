// Clean-room F1 witness for a finite SVA inside set.
module sva_inside (
  input logic clk,
  input logic [3:0] a,
  output logic [3:0] q
);
  assign q = a;
  assert property (@(posedge clk) a inside {4'b0, 4'b1, {4{1'b1}}});
endmodule
