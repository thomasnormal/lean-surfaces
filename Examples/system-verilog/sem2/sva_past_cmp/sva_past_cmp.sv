// Clean-room F1 witness for a sampled order comparison with $past.
module sva_past_cmp (
  input logic clk,
  input logic [3:0] a,
  input logic [3:0] b,
  output logic q
);
  assign q = a > b;
  assert property (@(posedge clk) a |-> a > $past(b));
endmodule
