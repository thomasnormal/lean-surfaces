// REFUSED by the always_comb alias guard (`AlwaysComb:alias-read`,
// LeanModels/Sv/CombAlias2.lean): the block reads `v`, which follows `t`
// through a CHAIN of two continuous assignments (`w = t`, `v = w`), and then
// writes `t`. The guard is transitive through chains of assigns (and port
// connections), not one hop. Icarus 12.0 is stale by one change on the
// chain too; Xcelium 24.03 and Verilator 5.042 settle (y = a).
module acg_alias_chain (
  input  logic [1:0] a,
  output logic [1:0] y
);
  logic [1:0] t, w, v;
  assign v = w;
  assign w = t;
  always_comb begin
    y = v;
    t = a;
  end
endmodule
