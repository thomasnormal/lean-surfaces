// A fixed unpacked array read at a GENVAR index (2026-10-28, WP2 repair;
// verifier row `uarr_rd`). The semantic tier declares one signal per cell
// and names the cell a constant select reaches; slang folds `m[i]` at the
// iteration it elaborated, so every iteration read `m[0]` (y = 0000 at
// a = 0110, where Icarus gives 0110). Refused:
// `ElementSelect:default-point-index`.
module cell_genvar (
  input  logic [3:0] a,
  output logic [3:0] y
);
  logic m [4];
  assign m[0] = a[0];
  assign m[1] = a[1];
  assign m[2] = a[2];
  assign m[3] = a[3];
  for (genvar i = 0; i < 4; i++) begin : g
    assign y[i] = m[i];
  end
endmodule
