// A latch written as always_comb: q holds while en is low. Its equation
// reads q itself, so the always_comb lowering refuses it
// (`LeanModels.Sv.Comb2ProcExample.latch_refused`). The differential row
// pins the holding behaviour of the settle semantics.
module latch_comb (
  input  logic en, d,
  output logic q
);
  always_comb begin
    if (en) q = d;
  end
endmodule
