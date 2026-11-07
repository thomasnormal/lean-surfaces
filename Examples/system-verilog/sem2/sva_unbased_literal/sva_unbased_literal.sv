// Clean-room F1 witness for an unbased unsized SVA literal.
module sva_unbased_literal (
  input logic clk,
  input logic [3:0] a,
  output logic q
);
  assign q = (a == 4'b0);
  assert property (@(posedge clk) a == '0);
endmodule
