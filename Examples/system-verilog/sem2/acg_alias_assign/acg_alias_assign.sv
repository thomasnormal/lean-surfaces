// REFUSED by the always_comb alias guard (`AlwaysComb:alias-read`,
// LeanModels/Sv/CombAlias2.lean; before round 6 of the svGolf gaps the
// self-read guard admitted it: the block reads `w`, a continuous-assign copy
// of `t`, and then writes `t`, two different variables).
// Measured (round-3 WP4 verifier, re-measured round 4; Xcelium 24.03 on all
// 8 cycles, round 3): Icarus 12.0 KEEPS `w` in the block's sensitivity list
// (`iverilog -g2012` netlist: `.event anyedge, w, a`, `w` a BUFZ functor of
// `t`) but propagates the copy SYNCHRONOUSLY inside the block's run: `t = a`
// changes `w` before the block reaches its event control, so nothing wakes
// it and y keeps the previous a (y lags a by one change). Xcelium 24.03,
// Yosys 0.53 and Verilator 5.042 re-run / settle the block: y = a, which is
// what the settle semantics computes. IEEE 1800-2023 §4.7/§4.8 permit both
// interleavings ("the simulator is correct in displaying either"), so the
// tools split and the block is refused. The former declaration
// (`iverilog-comb-assign-alias-sensitivity`) is retired with this row's
// flip to a loud-refusal row (docs/sv-oracle-disagreements.md).
module acg_alias_assign (
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
