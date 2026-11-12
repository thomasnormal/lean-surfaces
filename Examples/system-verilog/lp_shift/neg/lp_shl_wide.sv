// NEGATIVE FIXTURE: `S = 1 << N` is 0 in a 32-bit `int` from `N = 32` on (IEEE 1800-2023 §11.4.10: every bit is shifted
// out), while the summary's value of the definition is 2^N, out of the 32-bit range: there the tactics refuse rather than
// read it. (`1 << 40` with no parameter is refused at load: the loader's defaults check reads the definition unbounded.)
module lp_shl_wide #(parameter int N = 8) (input logic [7:0] a, output logic [7:0] y);
  localparam integer S = 1 << N;
  assign y = a;
endmodule
