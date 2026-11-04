// A fixed-width byte cast resizes the source before the 4-state to 2-state
// squash boundary.
module two_state_cast_widen (
  input  logic [3:0] a,
  output logic [7:0] y
);
  always_comb y = byte'(a);
endmodule
