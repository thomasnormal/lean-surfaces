// One driver per bit on an instance-free top (2026-10-28, WP2): the windows
// of a generate-for's continuous assigns depend on the genvar, so the
// extractor's literal-window overlap guard cannot see that `y[0]` and `y[1]`
// each get TWO drivers (i = 0, 1 and i = 2, 3). Icarus 12.0 refuses the
// design ("Unresolved net/uwire y cannot have multiple drivers"), Yosys 0.53
// reports "multiple conflicting drivers"; the model refuses it loudly
// (`PortConn:driver`, `PDesign.instantiateG2`) instead of resolving the two
// drivers by issue order.
module drv_genvar_ov (
  input  logic [3:0] a,
  output logic [1:0] y
);
  for (genvar i = 0; i < 4; i++) begin : g
    assign y[i/2] = a[i];
  end
endmodule
