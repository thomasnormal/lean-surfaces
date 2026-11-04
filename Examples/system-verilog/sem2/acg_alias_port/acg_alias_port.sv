// REFUSED by the always_comb alias guard (`AlwaysComb:alias-read`,
// LeanModels/Sv/CombAlias2.lean): an always_comb in a child whose input port
// `i` and output port `o` are connected to the SAME parent variable `w` (a
// port loop; it exists only after the hierarchy is flattened, which is where
// the guard runs). The block reads `i` and then writes `o`; before round 6 of
// the svGolf gaps the self-read guard admitted it (different variables).
// Measured (round-3 WP4 verifier, re-measured round 4; Xcelium 24.03 on all
// 8 cycles, round 3): Icarus 12.0 KEEPS `i` in the block's sensitivity list
// (`.event anyedge, i, a`, `i` a net on the variable node of `o`) but the
// write of `o` changes `i` SYNCHRONOUSLY inside the block's run, so nothing
// wakes it and y keeps the previous a. Xcelium 24.03 and Verilator 5.042
// re-run the block: y = a, which is what the settle semantics computes. IEEE
// 1800-2023 §4.7/§4.8 permit both interleavings, so the tools split and the
// block is refused. The former declaration
// (`iverilog-comb-port-loop-sensitivity`) is retired with this row's flip to
// a loud-refusal row (docs/sv-oracle-disagreements.md).
module acg_alias_port_leaf (
  input  logic [1:0] i, a,
  output logic [1:0] o, y
);
  always_comb begin
    y = i;
    o = a;
  end
endmodule

module acg_alias_port (
  input  logic [1:0] a,
  output logic [1:0] y
);
  logic [1:0] w;
  acg_alias_port_leaf u (.i(w), .a(a), .o(w), .y(y));
endmodule
