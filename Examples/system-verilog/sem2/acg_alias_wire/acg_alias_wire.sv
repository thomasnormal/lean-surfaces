// REFUSED by the alias guard (`AlwaysComb:alias-read`) since WP-PROC N2
// (2026-11-01): the single-driver net `w` is declared as the variable its
// `assign` writes, so the guard sees the copy. Before N2 an internal `wire`
// never reached the guard: `wire w;` was `Unsupported` `NetSymbol:net-z`
// (2026-10-28: an undriven net reads z, the semantic tier initializes every
// declaration to x, so every internal net was refused). The shape is the
// `acg_alias_assign` one with `w` a net: the block reads `w`, a copy of `t`,
// and then writes `t`. Measured (round 6, lane B): Icarus 12.0 shows y one
// change behind a, Xcelium 24.03 and Verilator 5.042 give y = a, so the tools
// split here as on `acg_alias_assign`; the alias guard follows the continuous
// assignments and never the kind of the declaration (the `#guard` pins of
// `CombAlias2.lean`), and a copy through an input port is `acg_alias_port`.
module acg_alias_wire (
  input  logic a,
  output logic y
);
  logic t;
  wire  w;
  assign w = t;
  always_comb begin
    y = w;
    t = a;
  end
endmodule
