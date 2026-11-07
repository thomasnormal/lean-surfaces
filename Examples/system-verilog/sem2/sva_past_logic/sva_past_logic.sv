// Clean-room F1 witness for a sampled $past value inside boolean logic.
module sva_past_logic (
  input logic clk,
  input logic a,
  input logic b,
  output logic q
);
  assign q = a && b;
  assert property (@(posedge clk) a |-> $past(b));
endmodule
