// WP-G S2: every operator of the second fragment in whole-signal and per-bit assigns, at a symbolic width:
// `~`, `!` (of a vector too), the six reductions, `&&`, `||`, `==`/`!=` over equal-width operands, `?:`
// with `~`, a reduction and a nested `?:` in its arms. All operands are exactly as wide as their target.
module ops_gen #(parameter int N = 4) (
  input  logic [N-1:0] a, b,
  input  logic         s,
  output logic [N-1:0] y_not, y_mux, y_xnor, y_nest,
  output logic         r_or, r_and, r_xor, r_nor, r_nand, r_xnor,
  output logic         z_lnot, q_land, q_lor, q_eq, q_ne, q_cond
);
  assign y_not  = ~a;
  assign y_mux  = s ? a : b;
  assign y_xnor = ~(a ^ b);
  assign y_nest = s ? ~a : (a[0] ? b : a);
  assign r_or   = |a;
  assign r_and  = &b;
  assign r_xor  = ^a;
  assign r_nor  = ~|b;
  assign r_nand = ~&a;
  assign r_xnor = ~^b;
  assign z_lnot = !b;
  assign q_land = s && a[0];
  assign q_lor  = a[0] || !b[0];
  assign q_eq   = a == b;
  assign q_ne   = a[0] != b[0];
  assign q_cond = (a[0] ^ b[0]) ? (&a) : ~|b;
endmodule
