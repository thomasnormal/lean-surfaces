// Round 7 folds (round 6 FOLDS verifier blocker 2, repro `vw_enw`): enum
// members whose values depend on the base width with no name in the
// initializer. IEEE 1800-2023 5.7.1 fills `'1` to the base width (EA = 15
// at the default N = 4, slang's value, which the envelope carried); Icarus
// 12.0 and the Yosys 0.53 netlist both give EA = 1, at the default too, and
// the model bound 15 at every N. Refused: EnumValueSymbol:unsized-literal-
// member (every point) and EnumValueSymbol:default-point-value (a base
// width that depends on the point).
module fold_enw #(parameter int N = 4) (
  input  logic [3:0] a,
  output logic [63:0] o1, o2, o3);
  typedef enum logic [N-1:0] {EA = '1, EB = 0} e_t;
  typedef enum logic [N-1:0] {KA = '0, KB} k_t;
  assign o1 = EA;
  assign o2 = KB;
  assign o3 = {a, EA};
endmodule
