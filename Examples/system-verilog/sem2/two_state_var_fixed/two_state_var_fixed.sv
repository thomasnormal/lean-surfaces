// A fixed-width bit temporary squashes X/Z when assigned from a logic input.
module two_state_var_fixed (
  input logic [7:0] a,
  output logic [7:0] y
);
  bit [7:0] t;
  always_comb begin
    t = a;
    y = t;
  end
endmodule
