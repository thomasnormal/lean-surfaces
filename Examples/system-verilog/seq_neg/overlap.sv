// Outside the FF-only profile: two always_ff processes write overlapping windows of q.
module overlap(input logic clk, input logic [3:0] a, b, output logic [3:0] q);
  always_ff @(posedge clk) q[3:0] <= a;
  always_ff @(posedge clk) q[2:0] <= b[2:0];
endmodule
