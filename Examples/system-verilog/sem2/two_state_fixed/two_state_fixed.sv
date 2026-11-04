// A fixed four-bit 2-state input: X/Z at the port boundary squash to zero.
// The symbolic tier retains the declaration's two-state contract and applies
// the same squash to both the direct copy and selected reads.
module two_state_fixed (
  input  bit [3:0] a,
  output logic [3:0] y,
  output logic [1:0] z
);
  always_comb begin
    y = a;
    z = {a[0], a[1]};
  end
endmodule
