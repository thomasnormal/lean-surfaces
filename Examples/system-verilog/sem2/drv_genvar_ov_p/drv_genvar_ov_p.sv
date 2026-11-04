// WP-R-D twin of drv_genvar_ov with a parameter on the top (never used): the windows of a generate-for's continuous assigns depend on the genvar, so y[0] and y[1] each get TWO drivers. slang's analysis pass reports it (`multiple-cont-assigns`) and the extractor refuses a design WITHOUT parameters on that report (`SlangAnalysis:MultipleContAssigns`, docs/sv-refusals.json policy of 2026-11-01), so drv_genvar_ov no longer reaches the Lean guard; this twin (a top with parameters has a verdict per point instead) does: `PortConn:driver` from `PDesign.instantiateG2` stays verified by run.
module drv_genvar_ov_p #(
  parameter int UNUSED = 0
) (
  input  logic [3:0] a,
  output logic [1:0] y
);
  for (genvar i = 0; i < 4; i++) begin : g
    assign y[i/2] = a[i];
  end
endmodule
