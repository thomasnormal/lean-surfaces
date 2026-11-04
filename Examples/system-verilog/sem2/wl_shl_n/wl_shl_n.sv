// WP-B2 gate 3 pin P13: `y = a << s` with a RUN-TIME 3-bit amount into an N-bit target: the left operand keeps its N bits, zeros shift in, an amount of N or more gives 0, an x/z bit of the left operand MOVES with the shift, an x/z bit of the amount makes every result bit x.
module wl_shl_n #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [2:0] s,
  output logic [N-1:0] y
);
  assign y = a << s;
endmodule
