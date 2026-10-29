// A self-read through a HELD value: when c is low, `y` reads the value `t`
// held before the block ran, and the block then overwrites `t` with `b`.
// The settle semantics gives y = c ? a : b (as Yosys 0.53 `proc` does);
// Icarus 12 shows y = the PREVIOUS b while c is low, since the block is
// never woken by its own write of `t` (IEEE 1800-2023 9.2.2.2.1). The
// always_comb profile refuses the body (`SymState.selfReadFree`;
// `LeanModels.Sv.Comb2ProcExample.held_refused`).
// Since 2026-10-28 (WP4) no answer is taken: the always_comb self-read guard
// refuses the block at instantiation (`AlwaysComb:self-read`,
// LeanModels/Sv/CombGuard2.lean; `Comb2ProcExample.held_guard`), and
// load_design_sv2 refuses this envelope.
module rbw_held (
  input  logic       c,
  input  logic [1:0] a, b,
  output logic [1:0] y
);
  logic [1:0] t;
  always_comb begin
    if (c) t = a;
    y = t;
    t = b;
  end
endmodule
