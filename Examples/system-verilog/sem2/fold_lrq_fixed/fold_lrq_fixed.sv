// The exact case of `fold_lrq`: `$left`/`$right`/`$low`/`$increment` of a
// signal whose range is written with literal bounds are the same at every
// point, and slang's fold is kept.
module fold_lrq_fixed #(parameter int N = 3) (
  input  logic [7:4]   u,
  input  logic [N-1:0] v,
  output logic [7:0]   o1,
  output logic [7:0]   o2,
  output logic [7:0]   o3,
  output logic [7:0]   o4,
  output logic [N-1:0] o5
);
  assign o1 = $left(u);
  assign o2 = $right(u);
  assign o3 = $low(u);
  assign o4 = $increment(u);
  assign o5 = v;
endmodule
