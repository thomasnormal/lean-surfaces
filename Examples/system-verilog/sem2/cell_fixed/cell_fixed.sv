// Control for `cell_genvar`/`cell_param` (2026-10-28, WP2 repair): in a
// family with an overridable parameter, unpacked-array indices that are
// literals or localparams are the same cell at every point, so they keep
// their one-signal-per-cell encoding (admitted at every W).
module cell_fixed #(
  parameter int W = 1
) (
  input  logic [3:0]   a,
  output logic [3:0]   y,
  output logic [W-1:0] z
);
  localparam int L = 2;
  logic m [4];
  assign m[0] = a[0];
  assign m[1] = a[1];
  assign m[L] = a[2];
  assign m[3] = a[3];
  assign y = {m[3], m[L], m[1], m[0]};
  assign z = {W{m[0]}};
endmodule
