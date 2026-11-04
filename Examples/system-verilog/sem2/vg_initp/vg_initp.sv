// An initialized output variable port partly driven by `assign`
// (2026-10-28, round 3 CX repair; round-2 WP2 verifier probe `vg_initp`):
// the same mixture as `vg_init` on a port. Icarus refuses it; loud
// (`ContinuousAssignSymbol:initialized-variable`).
module vg_initp (
  input  logic a,
  output logic [1:0] y = 2'b10
);
  assign y[0] = a;
endmodule
