// REFUSED by the clock discipline (`Clock:multiple`, WP-Q0): a second clock
// PORT. The cycle step ticks every edge process once, i.e. both clocks
// together, so `b` follows `a` within one cycle; independent or interleaved
// clocks are the sequential layer's later work.
module clk_two (
  input  logic clk1, clk2, d,
  output logic a, b
);
  always_ff @(posedge clk1) a <= d;
  always_ff @(posedge clk2) b <= a;
endmodule
