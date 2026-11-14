// NEGATIVE FIXTURE: a comparison used as a number (`(N > 2) + 1`), not as the condition of `?:`; an unused localparam of a
// plain buffer.
module lp_cmp_num #(parameter int N = 8) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  localparam integer C = (N > 2) + 1;
  assign y = a;
endmodule
