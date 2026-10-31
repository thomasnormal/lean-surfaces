// WP-G four-state contract: blocking assignments run in order inside the body: the last write to a window wins (y = a; y = b gives b), and a module-level temporary assigned then read in the same body carries the value just written (z = (a ^ b) & c). Pinned against Xcelium 24.03.
module wpg_order (
  input  logic a,
  input  logic b,
  input  logic c,
  output logic y,
  output logic z
);
  logic t;
  always_comb begin y = a; y = b; t = a ^ b; z = t & c; end
endmodule
