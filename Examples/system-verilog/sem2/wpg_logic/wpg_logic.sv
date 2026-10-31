// WP-G four-state contract (S2): logical `&&` and `||` (1-bit result). `&&` is 0 as soon as one operand is all-zero, 1 when both have a definite 1 bit, else x; `||` is 1 as soon as one operand has a definite 1 bit, 0 when both are all-zero, else x. Vector operands (`1x` counts as true, `0x` is unknown) and a negated operand. Pinned against Xcelium 24.03.
module wpg_logic (
  input  logic a,
  input  logic b,
  input  logic [1:0] v,
  input  logic [1:0] w,
  output logic la,
  output logic lo,
  output logic lva,
  output logic lvo,
  output logic lm,
  output logic ln
);
  assign la = a && b;
  assign lo = a || b;
  assign lva = v && w;
  assign lvo = v || w;
  assign lm = a && !b;
  assign ln = !(a || b);
endmodule
