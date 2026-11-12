// Clean-room wrong-answer witness: signed int addition/modulo and unary min.
module int32_const_add_unary_e #(parameter int N = 2) (
  output logic [31:0] add_mod_out,
  output logic [31:0] unary_min_out
);
  localparam int A = (N + 32'sd2147483647) % 100;
  localparam int MIN = -2147483648;
  localparam int U = -MIN;
  assign add_mod_out = A;
  assign unary_min_out = U;
endmodule
