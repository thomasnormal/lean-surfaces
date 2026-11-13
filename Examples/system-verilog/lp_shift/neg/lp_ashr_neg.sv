// NEGATIVE FIXTURE: `(N - 16) >>> (N - 9)` at `N < 9` shifts a negative `int` (where `N < 16`) by a negative amount.
// IEEE 1800-2023 §11.4.10 reads the amount as unsigned, so every bit is shifted out and the arithmetic shift fills the
// result with the sign bit: -1 at `N = 8` (local Icarus Verilog 12.0 and Verilator 5.042 print -1 for `-8 >>> -1`). The
// instantiation gives 0 for every negative amount (`evalIntExactRec`), so the two readings part there: the tactics refuse
// for every `N ≥ 1` and read the design for `N ≥ 16`. At the default `N = 32` both give `16 >>> 23` = 0.
module lp_ashr_neg #(parameter int N = 32) (input logic [N-1:0] a, output logic [N-1:0] y);
  localparam integer S = (N - 16) >>> (N - 9);
  assign y = a;
endmodule
