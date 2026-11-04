// Round 6 folds: the untyped constants `Constant:untyped-width` admits —
// no + - * or ** on the context chain (Icarus 12.0 gives them their own
// width, measured with $bits): a shift (`(N + 1) >> 1` is 32 bits), a
// division (`N / 2`), a comparison, a plain reference.
module fold_uwok #(parameter int N = 8) (
  input  logic [3:0] a,
  output logic [63:0] o1, o2, o3, o4);
  localparam D = (N + 1) >> 1;
  localparam E = N / 2;
  localparam F = N == 8;
  localparam G = N;
  assign o1 = {a, D};
  assign o2 = {a, E};
  assign o3 = a + F;
  assign o4 = {a, G};
endmodule
