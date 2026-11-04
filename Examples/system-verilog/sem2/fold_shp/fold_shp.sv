// Round 7 folds (round 6 FOLDS verifier blocker 3, repro `vw_shp`): an
// untyped PARAMETER default `P = 1 << N`, 32 + N bits in Icarus 12.0 and 32
// in slang and the Yosys 0.53 netlist. Refused: Constant:untyped-width.
module fold_shp #(parameter int N = 8, parameter P = 1 << N) (
  input  logic [3:0] a,
  output logic [79:0] o1);
  assign o1 = {a, P};
endmodule
