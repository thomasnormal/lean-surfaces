// NEGATIVE FIXTURE: `Z = 2 ** (N - 5)` has a negative exponent where N < 5, which the instantiation refuses
// (`evalIntExactRec`: "negative exponent"); an unused localparam of a plain buffer.
module lp_pow_neg #(parameter int N = 8) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  localparam integer Z = 2 ** (N - 5);
  assign y = a;
endmodule
