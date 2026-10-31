// WP-G: a block-local temporary (`begin logic t; ...`) has the value semantics of a module-level temporary (Xcelium 24.03). The symbolic tier refuses it today (the envelope's LocalDecl statement is not ingested): REFUSAL row, the Xcelium trace is quoted in `measured`.
module wpg_local (
  input  logic a,
  input  logic b,
  input  logic c,
  output logic y
);
  always_comb begin logic t; t = a ^ b; y = t & c; end
endmodule
