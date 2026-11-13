// FORMERLY NEGATIVE: `(N - 16) >> 1` is a logical shift of a negative `int` where `N < 16` (IEEE 1800-2023 §11.4.10:
// the 32-bit pattern shifted with zeros, 2147483644 at `N = 8`). The instantiation reads it so too (master 853147a63),
// and the tactics read it for every `N ≥ 1` (`../comb_errors.lean`).
module lp_shr_neg #(parameter int N = 32) (input logic [N-1:0] a, output logic [N-1:0] y);
  localparam integer S = (N - 16) >> 1;
  assign y = a;
endmodule
