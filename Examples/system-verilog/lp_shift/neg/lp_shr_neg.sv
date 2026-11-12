// NEGATIVE FIXTURE: `(N - 16) >> 1` is a logical shift of a negative `int` where `N < 16` (IEEE 1800-2023 §11.4.10:
// the pattern shifted with zeros), which the instantiation refuses ("'>>' of a negative constant"); a theorem for every
// `N ≥ 1` cannot be stated over it, and the tactics refuse, naming the decision.
module lp_shr_neg #(parameter int N = 32) (input logic [N-1:0] a, output logic [N-1:0] y);
  localparam integer S = (N - 16) >> 1;
  assign y = a;
endmodule
