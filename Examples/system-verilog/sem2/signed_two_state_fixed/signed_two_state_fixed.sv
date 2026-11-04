// A fixed-width signed 2-state input. X/Z stimulus is squashed at the port
// boundary, while the retained signed declaration controls the source value.
module signed_two_state_fixed (
  input  bit signed [3:0] a,
  output logic [3:0] raw,
  output logic [3:0] abs_bits
);
  always_comb begin
    raw = a;
    abs_bits = a[3] ? (~a + 4'b0001) : a;
  end
endmodule
