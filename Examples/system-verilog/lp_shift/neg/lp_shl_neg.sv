// NEGATIVE FIXTURE: a shift by `N - 2`, a negative amount at `N = 1`. The instantiation refuses a negative amount
// ("negative shift"), so a theorem for every `N ≥ 1` cannot be stated over it; the tactics refuse, naming the decision.
module lp_shl_neg #(parameter int N = 8) (input logic [N-1:0] a, output logic [N-1:0] y);
  localparam integer S = 1 << (N - 2);
  assign y = a;
endmodule
