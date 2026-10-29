// A latch that reads its own held value (ADMITTED): when en is low `q` keeps
// the value it had, and `y = q` reads it; nothing the block reads is written
// later on the same path, so one run per wake-up is already the block's
// fixpoint and the settle semantics agrees with an event-driven simulator
// (LeanModels/Sv/CombGuard2.lean, `CombGuard2Sound.combAdmits_idem`).
module acg_latch_read (
  input  logic en, d,
  output logic q, y
);
  always_comb begin
    if (en) q = d;
    y = q;
  end
endmodule
