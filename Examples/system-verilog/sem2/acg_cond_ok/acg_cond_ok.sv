// A read in an `if` condition AFTER the block wrote the variable (ADMITTED).
// Admitted by the always_comb self-read guard (LeanModels/Sv/CombGuard2.lean).
module acg_cond_ok (
  input  logic a, b, c,
  output logic y
);
  logic t;
  always_comb begin
    t = a;
    if (t) y = b;
    else y = c;
  end
endmodule
