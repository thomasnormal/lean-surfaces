// Round 4 folds, the unwrapped encoding `_sym_unsigned_simple_operand`
// keeps: a signed int parameter assigned to a typed localparam of the same
// width at the default N = 32 is a bare parameter reference in the envelope
// (an assignment-like conversion keeps the right-hand side's signedness,
// IEEE 1800-2023 10.7, 11.8.2), so at N = 40 it is sign-extended — as in
// Icarus 12.0 and Yosys 0.53.
module fold_rlpsgn #(parameter int N = 32, parameter int P = -3) (
  input  logic [N-1:0] a,
  output logic [N-1:0] o1,
  output logic [N-1:0] o2);
  localparam logic [N-1:0] L1 = P;
  localparam logic [N-1:0] L2 = P - 1;
  assign o1 = L1 ^ a;
  assign o2 = L2 ^ a;
endmodule
