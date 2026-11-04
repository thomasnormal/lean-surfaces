// Two `always_comb` blocks on parameter-dependent windows (2026-10-28, WP2
// repair): disjoint at the default K = 1 (admitted), both on `y[0]` at K = 0
// (IEEE 1800-2023 §9.2.2.2; loud, `PortConn:driver`).
module drv_pw_par #(
  parameter int K = 1
) (
  input  logic [1:0] a,
  output logic [1:0] y
);
  always_comb y[K] = a[1];
  always_comb y[0] = a[0];
endmodule
