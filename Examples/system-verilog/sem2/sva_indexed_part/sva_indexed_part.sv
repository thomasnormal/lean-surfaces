// Clean-room F1 witness for indexed part-selects and sized vector literals.
module sva_indexed_part (
  input logic clk,
  input logic [7:0] a,
  input logic [2:0] base
);
  assert property (@(posedge clk) a[base +: 2] == 2'b01);
endmodule
