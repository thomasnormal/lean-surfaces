// Clean-room F1 witness for logical implication and equivalence expressions.
module sva_logical_ops (
  input logic clk,
  input logic a,
  input logic b,
  output logic q
);
  assign q = a;
  assert property (@(posedge clk) (a <-> b));
  assert property (@(posedge clk) (a |-> (a -> b)));
endmodule
