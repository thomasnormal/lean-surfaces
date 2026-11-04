// WP-R-D twin of drv_pw_lit with a parameter on the top (never used): the same two `always_comb` writers of y[0], IEEE 1800-2023 9.2.2.2. slang's analysis pass reports it (`multiple-always-assigns`) and the extractor refuses a design WITHOUT parameters on that report (`SlangAnalysis:MultipleAlwaysAssigns`, docs/sv-refusals.json policy of 2026-11-01), so drv_pw_lit no longer reaches the Lean guard. A top with parameters has a verdict per point instead (the probe sidecar's `frontend_errors`), so this twin does reach it: `PortConn:driver`, `driversOk`'s exclusivity clause, stays verified by run.
module drv_pw_lit_p #(
  parameter int UNUSED = 0
) (
  input  logic [1:0] a,
  output logic [1:0] y
);
  always_comb y[0] = a[0];
  always_comb y[0] = a[1];
  always_comb y[1] = a[0];
endmodule
