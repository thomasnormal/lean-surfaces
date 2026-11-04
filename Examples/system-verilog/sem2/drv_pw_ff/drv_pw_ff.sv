// Generate-loop `always_ff` writers (2026-10-28, WP2 repair): at the default
// D = 2 both flops write `y[0]`, which IEEE 1800-2023 §9.2.2.4 forbids
// (loud, `PortConn:driver`); at D = 1 they write `y[0]` and `y[1]` —
// distinct longest static prefixes, legal, admitted.
module drv_pw_ff #(
  parameter int D = 2
) (
  input  logic       clk,
  input  logic [1:0] a,
  output logic [1:0] y
);
  for (genvar i = 0; i < 2; i++) begin : g
    always_ff @(posedge clk) y[i/D] <= a[i];
  end
endmodule
