// An always_comb that reads `w`, a continuous-assign copy of `t`, and then
// writes `t` (ADMITTED by the self-read guard: the block reads no bit it
// writes; `w` and `t` are different variables).
// Measured (round-3 WP4 verifier, re-measured round 4): Icarus 12.0 KEEPS
// `w` in the block's sensitivity list (`iverilog -g2012` netlist:
// `.event anyedge, w, a`, `w` a BUFZ functor of `t`) but propagates the
// copy SYNCHRONOUSLY inside the block's run: `t = a` changes `w` before
// the block reaches its event control, so nothing wakes it and y keeps the
// previous a. Xcelium 24.03, Verilator 5.042 and Yosys 0.53 re-run / settle
// the block: y = a. IEEE 1800-2023 §4.7/§4.8 permit both interleavings
// ("the simulator is correct in displaying either"), so this is a tool
// split, not an Icarus departure from a rule; the model gives y = a and the
// Icarus trace is declared on the harness/sv/cases2.json row
// (`iverilog-comb-assign-alias-sensitivity`; docs/sv-oracle-disagreements.md).
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
