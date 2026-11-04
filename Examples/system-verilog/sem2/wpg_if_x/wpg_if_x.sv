// WP-G four-state contract: a procedural `if` takes the ELSE branch unless the condition has a definite 1 bit (1-bit x/z -> else; 2-bit: 1x, x1, 1z are true, 0x, xx, zz are false). `if (!c)` with c = x is the else branch, NOT the swap of `if (c)` (y3 vs y4 differ at c = x); `if (~c)` likewise. Pinned against Xcelium 24.03.
module wpg_if_x (
  input  logic c,
  input  logic a,
  input  logic b,
  input  logic [1:0] v,
  output logic y1,
  output logic y2,
  output logic y3,
  output logic y4,
  output logic y5
);
  always_comb begin if (c) y1 = a; else y1 = b; end
  always_comb begin if (v) y2 = a; else y2 = b; end
  always_comb begin if (!c) y3 = a; else y3 = b; end
  always_comb begin if (c) y4 = b; else y4 = a; end
  always_comb begin if (~c) y5 = a; else y5 = b; end
endmodule
