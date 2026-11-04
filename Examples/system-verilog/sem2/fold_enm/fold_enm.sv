// Round 6 folds (the class behind the round 5 FOLDS verifier's blockers: an
// envelope value fixed at the default point). An enum whose member VALUES
// depend on a parameter: the envelope's EnumType carries each member's
// DEFAULT-point value, and Lean bound those at every point — `EB` read 5 at
// N = 5 (default N = 3) where Icarus 12.0 and the Yosys 0.53 netlist give 7.
// A reference to a member of such an enum is refused by the extractor:
// EnumValueSymbol:default-point-value. A fixed enum stays admitted
// (`fold_enf`).
module fold_enm #(parameter int N = 3) (
  input  logic [3:0] a,
  output logic [7:0] o1, o2);
  typedef enum logic [7:0] {EA = N, EB = N + 2} e_t;
  assign o1 = EB;
  assign o2 = EA + a;
endmodule
