// Blocking edge assignments expose an intermediate write under IEEE 1800-2023 §4.7.
module preempt_blocking (
  input logic clk,
  input logic a,
  input logic b,
  output logic q,
  output logic r
);
  always @(posedge clk) q = a;
  always @(posedge clk) r = q;
endmodule
