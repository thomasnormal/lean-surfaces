// A fixed packed assignment pattern uses the existing Concat expression path.
module pattern_fixed (
  input logic [3:0] a,
  output logic [3:0] y
);
  always_comb y = '{a[3], a[2], 1'bx, 1'b0};
endmodule
