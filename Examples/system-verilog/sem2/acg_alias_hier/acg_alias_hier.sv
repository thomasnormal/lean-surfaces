// REFUSED by the always_comb alias guard (`AlwaysComb:alias-read`,
// LeanModels/Sv/CombAlias2.lean): the alias is INSIDE the instantiated
// module (`assign w = t;` and an always_comb that reads `w`, then writes
// `t`). The guard runs on the flattened design, where the child's signals are
// `u.w`, `u.t`, and the message names the instance.
module acg_alias_hier_leaf (
  input  logic [1:0] a,
  output logic [1:0] y
);
  logic [1:0] t, w;
  assign w = t;
  always_comb begin
    y = w;
    t = a;
  end
endmodule

module acg_alias_hier (
  input  logic [1:0] a,
  output logic [1:0] y
);
  acg_alias_hier_leaf u (.a(a), .y(y));
endmodule
