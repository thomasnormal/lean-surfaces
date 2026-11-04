// Round 6 folds: an INT-class override with + - * into an UNTYPED child
// parameter, which takes the override's type (IEEE 1800-2023 6.20.2): 32
// bits in slang and the Yosys 0.53 netlist, the lossless 33 in Icarus 12.0
// (`{a, W}` in the child: 0x600000009 against 0x300000009 at a = 3, N = 8).
// Refused by the extractor: InstanceSymbol:override-untyped-width. A leaf
// override (`.W(N)`) and one into a typed parameter stay admitted
// (`fold_uwovl`).
module fold_uwovr_c #(parameter W = 8) (
  input  logic [3:0] a,
  output logic [63:0] o);
  assign o = {a, W};
endmodule
module fold_uwovr #(parameter int N = 8) (
  input  logic [3:0] a,
  output logic [63:0] o1);
  fold_uwovr_c #(.W(N + 1)) u1 (.a(a), .o(o1));
endmodule
