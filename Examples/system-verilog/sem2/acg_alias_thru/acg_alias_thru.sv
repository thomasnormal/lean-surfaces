// REFUSED by the always_comb alias guard (`AlwaysComb:alias-read`,
// LeanModels/Sv/CombAlias2.lean): the copy of `t` is made by a CHILD. The
// parent's block reads `w` and then writes `t`; `w` is the child's output
// `o`, which the child assigns from its input `i`, which the parent ties to
// `t`. After flattening the path `t` -> `u.i` -> `u.o` -> `w` is three
// continuous assignments (two port connections around the child's own
// `assign o = i;`), none of them in the parent's module: the guard follows
// the dependency path through the flat design, never the kind of functor and
// never the module the assign sits in. Round 6, lane B (docs/sv-oracle-
// disagreements.md, "Icarus propagates a copy inside the block's own run").
module acg_alias_thru_buf (
  input  logic [1:0] i,
  output logic [1:0] o
);
  assign o = i;
endmodule

module acg_alias_thru (
  input  logic [1:0] a,
  output logic [1:0] y
);
  logic [1:0] t, w;
  acg_alias_thru_buf u (.i(t), .o(w));
  always_comb begin
    y = w;
    t = a;
  end
endmodule
