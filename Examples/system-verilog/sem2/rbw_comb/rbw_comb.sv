// An always_comb that reads `t` before writing it. The settle semantics
// re-runs the block until nothing changes and gives y = a (Yosys 0.53 `proc`
// synthesizes the same `assign y = a`); an event-driven simulator runs the
// block once per change of `a` and is never woken by its own write of `t`
// (IEEE 1800-2023 9.2.2.2.1), so Icarus 12 shows y = the PREVIOUS a. The
// always_comb profile refuses the body (`SymState.selfReadFree`;
// `LeanModels.Sv.Comb2ProcExample.rbw_refused`).
// Since 2026-10-28 (WP4) no answer is taken: the always_comb self-read guard
// refuses the block at instantiation (`AlwaysComb:self-read`,
// LeanModels/Sv/CombGuard2.lean; `Comb2ProcExample.rbw_guard`), and
// load_design_sv2 refuses this envelope.
module rbw_comb (
  input  logic [1:0] a,
  output logic [1:0] y
);
  logic [1:0] t;
  always_comb begin
    y = t;
    t = a;
  end
endmodule
