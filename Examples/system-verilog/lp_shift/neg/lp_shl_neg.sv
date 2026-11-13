// NEGATIVE FIXTURE: a shift by `N - 2`, a negative amount at `N = 1`, where `S` is 0 (IEEE 1800-2023 §11.4.10: the amount is
// unsigned, every bit is shifted out) and the summary's unbounded `2^(2^32-1)` is no `int`; the tactics refuse, naming it.
module lp_shl_neg #(parameter int N = 8) (input logic [N-1:0] a, output logic [N-1:0] y);
  localparam integer S = 1 << (N - 2);
  assign y = a;
endmodule
