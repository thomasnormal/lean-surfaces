// Two edge processes with a cross-process read/write dependency.
// The ordinary process-atomic profile can run this design; the optional
// IEEE §4.7 preemption profile refuses it until E has an intra-process choice.
module preempt_profile (
  input logic clk,
  input logic a,
  input logic b,
  output logic q,
  output logic r
);
  always_ff @(posedge clk) q <= a;
  always_ff @(posedge clk) r <= q;
endmodule
