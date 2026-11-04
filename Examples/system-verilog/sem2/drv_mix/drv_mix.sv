// A continuous and a procedural writer of one variable (2026-10-28, WP2
// repair). IEEE 1800-2023 §6.5 forbids the mixture only on one longest
// static prefix: at the default K = 1 the `assign` drives `y[1]` and the
// `always_comb` writes `y[0]` — legal, admitted; at K = 0 both are on
// `y[0]` (loud, `PortConn:driver`).
module drv_mix #(
  parameter int K = 1
) (
  input  logic a,
  input  logic b,
  output logic [1:0] y
);
  always_comb y[0] = a;
  assign y[K] = b;
endmodule
