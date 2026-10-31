// WP-G four-state contract: `!` is LOGICAL and self-determined (a 1-bit result, then zero-extended: !x = x, !2'b1x = 0, !2'b0x = x, !2'b00 = 1), `~` is BITWISE and context-determined (the operand is extended to the context FIRST: ~a assigned to 4 bits is 111~a). Pinned against Xcelium 24.03.
module wpg_not (
  input  logic a,
  input  logic [1:0] v,
  output logic n1,
  output logic b1,
  output logic [3:0] n4,
  output logic [3:0] b4,
  output logic nl,
  output logic [1:0] nb,
  output logic [3:0] nl4,
  output logic [3:0] nb4,
  output logic nn,
  output logic nr
);
  assign n1 = !a;
  assign b1 = ~a;
  assign n4 = !a;
  assign b4 = ~a;
  assign nl = !v;
  assign nb = ~v;
  assign nl4 = !v;
  assign nb4 = ~v;
  assign nn = !(!v);
  assign nr = !(~v);
endmodule
