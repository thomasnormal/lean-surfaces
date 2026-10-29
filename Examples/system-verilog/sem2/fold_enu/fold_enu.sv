// Round 7 folds (round 6 FOLDS verifier blocker 2): the single-point form
// of `fold_enw`. `typedef enum logic [3:0] {EA = '1, EB = 0}` has EA = 15
// in slang (IEEE 1800-2023 5.7.1) and EA = 1 in Icarus 12.0 and the Yosys
// 0.53 netlist; the tools split from the LRM in a module with one point.
// Refused: EnumValueSymbol:unsized-literal-member.
module fold_enu (
  input  logic [3:0] a,
  output logic [63:0] o1, o2);
  typedef enum logic [3:0] {EA = '1, EB = 0} e_t;
  assign o1 = EA;
  assign o2 = {a, EA};
endmodule
