// Round 7 folds (round 6 FOLDS verifier blocker 3, repro `vw_sho`): an
// INT-class override `.W(1 << N)` into an UNTYPED child parameter, which
// takes the override's type: 32 bits in slang and the Yosys 0.53 netlist,
// 32 + N in Icarus 12.0. Refused: InstanceSymbol:override-untyped-width.
module fold_sho_c #(parameter W = 8) (
  input  logic [3:0] a,
  output logic [79:0] o);
  assign o = {a, W};
endmodule
module fold_sho #(parameter int N = 8) (
  input  logic [3:0] a,
  output logic [79:0] o1);
  fold_sho_c #(.W(1 << N)) u1 (.a(a), .o(o1));
endmodule
