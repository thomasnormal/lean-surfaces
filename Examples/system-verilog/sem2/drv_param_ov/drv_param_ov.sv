// One driver per bit on an instance-free top (2026-10-28, WP2): the second
// window's position depends on the parameter. At the default `K = 2` the
// two windows tile `y` (admitted, compared with Icarus); at `K = 1` both
// assigns drive `y[1]` (Icarus refuses the design, Yosys reports
// conflicting drivers), and the model refuses that point loudly
// (`PortConn:driver`) — the defaults-only extractor guard never sees it.
module drv_param_ov #(parameter int K = 2) (
  input  logic [3:0] a,
  output logic [3:0] y
);
  assign y[1:0]   = a[1:0];
  assign y[K+1:K] = a[3:2];
endmodule
