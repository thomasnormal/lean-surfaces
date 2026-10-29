// REFUSED, but not by the alias guard: an internal `wire` never reaches it.
// `wire w;` is `Unsupported` `NetSymbol:net-z` (2026-10-28: an undriven net
// reads z, the semantic tier initializes every declaration to x, so every
// internal net is refused), and the model is loud on the whole design. The
// shape is the `acg_alias_assign` one with `w` a net: the block reads `w`,
// a copy of `t`, and then writes `t`. Measured (round 6, lane B): Icarus
// 12.0 shows y one change behind a, Xcelium 24.03 and Verilator 5.042 give
// y = a, so were nets ever admitted the tools would split here too; the
// alias guard looks at the continuous assignments and never at the kind of
// the declaration, and would refuse it (the `#guard` pins of
// `CombAlias2.lean`). The nets the tier DOES admit are input ports, and a
// copy through one is `acg_alias_port` (the guard reads `u.i`, a net).
// Also refused earlier: `wire [1:0] w;` (`unrecoverable packed dimensions`)
// and `wire w = t;` (`non-literal initializer`).
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
