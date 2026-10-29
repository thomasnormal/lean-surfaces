// A declaration initializer plus a continuous assign on one variable
// (2026-10-28, round 3 CX repair; round-2 WP2 verifier probe `vg_init`).
// The initializer is a procedural write (§10.5) the one-driver rule never
// sees, so the design mixes continuous and procedural writers of `t[0]`
// (§6.5). slang -Wmixed-var-assigns, Icarus "Unable to assign to unresolved
// wires", Yosys a conflicting constant driver: loud
// (`ContinuousAssignSymbol:initialized-variable`).
module vg_init (
  input  logic a,
  output logic [1:0] y
);
  logic [1:0] t = 2'b10;
  assign t[0] = a;
  assign y = t;
endmodule
