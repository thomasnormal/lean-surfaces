// NEGATIVE FIXTURE: `Z = 2 ** N` is no 32-bit `int` from N = 31 on (the instantiation wraps it: 2 ** 31 is -2^31, 2 ** 32
// is 0), so a statement needs a bound of N; an unused localparam of a plain buffer.
module lp_pow_wide #(parameter int N = 8) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  localparam integer Z = 2 ** N;
  assign y = a;
endmodule
