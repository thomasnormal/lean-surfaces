// Round 6 folds: the admitted companion of `fold_enm` — an enum in a
// parametric family whose member values are literals (and implicit
// successors), the same at every point.
module fold_enf #(parameter int N = 8) (
  input  logic [3:0] a,
  input  logic [N-1:0] b,
  output logic [7:0] o1, o2,
  output logic [63:0] o3);
  typedef enum logic [7:0] {EA = 2, EB, EC = 2 + 3} e_t;
  assign o1 = EB;
  assign o2 = EC + a;
  assign o3 = EC + b;
endmodule
