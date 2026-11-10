// IEEE 1800-2023 §9.4.2.3: an iff guard qualifies its own event.
module reset_event_iff (
  input logic clk, rn, rp, en, d,
  output logic guarded_n, guarded_p, plain_n, plain_p
);
  always_ff @(posedge clk or negedge rn iff en)
    if (!rn) guarded_n <= 1'b0; else guarded_n <= d;
  always_ff @(posedge clk or posedge rp iff en)
    if (rp) guarded_p <= 1'b0; else guarded_p <= d;
  always_ff @(posedge clk or negedge rn)
    if (!rn) plain_n <= 1'b0; else plain_n <= d;
  always_ff @(posedge clk or posedge rp)
    if (rp) plain_p <= 1'b0; else plain_p <= d;
endmodule
