// Two `always_comb` writers of one bit (2026-10-28, WP2 repair): IEEE
// 1800-2023 §9.2.2.2 forbids any other process writing a variable an
// `always_comb` writes (applied per longest static prefix, §11.5.3 — so
// `y[1]`, written by a third block, is fine). slang reports it
// (`-Wmultiple-always-assigns`); Icarus 12.0 runs it and gives `y[0]` the
// value of whichever block ran last. The model refuses it loudly
// (`PortConn:driver`, `driversOk`'s exclusivity clause) instead of ordering
// the two writes by process order.
module drv_pw_lit (
  input  logic [1:0] a,
  output logic [1:0] y
);
  always_comb y[0] = a[0];
  always_comb y[0] = a[1];
  always_comb y[1] = a[0];
endmodule
