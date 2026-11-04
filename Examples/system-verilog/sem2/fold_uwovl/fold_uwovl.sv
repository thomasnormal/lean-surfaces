// Round 6 folds: the admitted companions of `fold_uwovr` — a LEAF override
// into an untyped child parameter (`.W(N)`: an `int` in every tool) and a
// `+` override into an `int`-typed one (32 bits in every tool).
module fold_uwovl_c #(parameter W = 8, parameter int V = 3) (
  input  logic [3:0] a,
  output logic [63:0] o, p);
  assign o = {a, W};
  assign p = {a, V};
endmodule
module fold_uwovl #(parameter int N = 8) (
  input  logic [3:0] a,
  output logic [63:0] o1, o2);
  fold_uwovl_c #(.W(N), .V(N + 1)) u1 (.a(a), .o(o1), .p(o2));
endmodule
