// WP-G: a block-local temporary (`begin logic t; ...`) has the value semantics of a module-level temporary (Xcelium 24.03). Since WP-PROC L1 (2026-11-01) the symbolic tier hoists it to a module variable, so the row is simulated and Xcelium-pinned (it was a REFUSAL row: the envelope's LocalDecl statement was not ingested).
module wpg_local (
  input  logic a,
  input  logic b,
  input  logic c,
  output logic y
);
  always_comb begin logic t; t = a ^ b; y = t & c; end
endmodule
