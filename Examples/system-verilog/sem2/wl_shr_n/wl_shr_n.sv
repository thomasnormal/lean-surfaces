// WP-B2 gate 3 pin P14: `y = a >> s` (logical right shift) with a run-time 3-bit amount: zeros shift in, an amount of N or more gives 0, x/z bits of the operand move, an x/z bit of the amount makes every result bit x.
module wl_shr_n #(parameter int N = 4) (
  input  logic [N-1:0] a,
  input  logic [2:0] s,
  output logic [N-1:0] y
);
  assign y = a >> s;
endmodule
