// An initialized parent variable driven through an instance output
// (2026-10-28, round 3 CX repair; round-2 WP2 verifier probe `vh_init`):
// an output connection is a continuous driver of its actual, so this is
// `vg_init` across a hierarchy. Icarus and slang reject it the same way;
// loud (`PortConnection:initialized-variable`).
module vh_initc (
  input  logic a,
  output logic o
);
  assign o = ~a;
endmodule

module vh_init (
  input  logic a,
  output logic [1:0] y
);
  logic [1:0] t = 2'b10;
  vh_initc u (.a(a), .o(t[0]));
  assign y = t;
endmodule
