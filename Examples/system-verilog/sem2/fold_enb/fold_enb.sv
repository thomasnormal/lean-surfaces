// Round 7 folds (round 6 FOLDS verifier blocker 2): an enum whose BASE width
// depends on the point. The envelope carries the DEFAULT point's member
// values (N = 4), which Lean truncates to the point's base width: at N = 3
// `SA = 9` does not fit (slang: EnumValueOutOfRange) and Lean read 1; at
// N = 1 `T2` (2) does not fit and Lean read 0. Every member of such an enum
// is refused, the literal FSM form `{T0, T1, T2}` at points where it fits
// too (a recorded over-refusal): EnumValueSymbol:default-point-value.
module fold_enb #(parameter int N = 4) (
  input  logic [3:0] a,
  output logic [63:0] o1, o2, o3);
  typedef enum logic [N-1:0] {SA = 9, SB = 2} s_t;
  typedef enum logic [N-1:0] {T0, T1, T2} t_t;
  assign o1 = SA;
  assign o2 = {a, SA};
  assign o3 = T2 + a;
endmodule
