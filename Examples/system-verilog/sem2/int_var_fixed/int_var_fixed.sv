// A fixed 32-bit two-state int temporary squashes X/Z at assignment.
module int_var_fixed (
  input logic [31:0] a,
  output logic [31:0] y
);
  int t;
  always_comb begin
    t = a;
    y = t;
  end
endmodule
