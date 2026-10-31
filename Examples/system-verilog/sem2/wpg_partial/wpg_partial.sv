// WP-G no-latch rule: each bit of y is written on ONE path only; the other bit keeps its previous value (x before the first write). The settle semantics admits and runs it (CombGuard2 admits latches), the proof layer's lowering refuses it (selfReadFree). Pinned against Xcelium 24.03.
module wpg_partial (
  input  logic c,
  input  logic a,
  input  logic b,
  output logic [1:0] y
);
  always_comb begin if (c) y[0] = a; else y[1] = b; end
endmodule
