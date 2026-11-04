// Round 5 folds (verifier repro vq_ovr2): an INT-class context-propagating
// override into a child parameter whose type width depends on another
// overridden parameter. At N = 1 the child's P is 41 bits: `N << 40` is
// -2^40 there (Icarus 12.0, IEEE 1800-2023 10.8, slang) and 0 in the Yosys
// 0.53 netlist; the envelope's override root carried the DEFAULT point's 40
// bits, where both readings are 0, so the model ran silently. Refused.
module fold_ovrw_c #(parameter int W = 40, parameter logic signed [W-1:0] P = 0) (
  output logic [63:0] o);
  assign o = P;
endmodule
module fold_ovrw #(parameter int N = 0) (
  input  logic [3:0] a,
  output logic [63:0] o1);
  fold_ovrw_c #(.W(N + 40), .P(N << 40)) u1 (.o(o1));
endmodule
