// REFUSED by the always_comb alias guard (`AlwaysComb:alias-read`,
// LeanModels/Sv/CombAlias2.lean) although every tool agrees on this one:
// the copy is INVERTING (`assign w = ~t;`), Icarus 12.0 schedules a NOT
// functor and so re-runs the block (y = ~a, as Xcelium 24.03 and Verilator
// 5.042). The guard follows the dependency path, never the kind of functor a
// simulator builds for it (`assign w = t;` gives the stale answer in Icarus),
// so this block is refused with the others.
module acg_alias_not (
  input  logic [1:0] a,
  output logic [1:0] y
);
  logic [1:0] t, w;
  assign w = ~t;
  always_comb begin
    y = w;
    t = a;
  end
endmodule
