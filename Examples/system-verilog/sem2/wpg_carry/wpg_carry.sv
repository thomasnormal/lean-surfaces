// WP-G four-state contract and the Gate 2/3 cell: co = p ? c : a written as an if/else, s = p ^ c in the same body (multi-target), and the one-target twin. A z carry-in passes through the TAKEN arm unchanged (co = z at p = 1, c = z), an x/z propagate takes the else arm (co = a). Pinned against Xcelium 24.03.
module wpg_carry (
  input  logic p,
  input  logic c,
  input  logic a,
  output logic co,
  output logic s,
  output logic co1
);
  always_comb begin if (p) co = c; else co = a; s = p ^ c; end
  always_comb begin if (p) co1 = c; else co1 = a; end
endmodule
